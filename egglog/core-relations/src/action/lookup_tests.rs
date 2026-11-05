use super::{Bindings, Instr, LookupOutput, mask::MaskIter};
use crate::{
    ColumnId, Constraint, Database, ExecutionState, MutationBuffer, Offset, QueryEntry, Row, RowId,
    SortedWritesTable, Subset, SubsetRef, Table, TableChange, TableSpec, TableVersion, Value,
    Variable, action::mask::Mask, numeric_id::NumericId, pool::PoolSet, table_shortcuts::v,
};
use std::{
    any::Any,
    sync::{
        Arc,
        atomic::{AtomicUsize, Ordering},
    },
};

// Count selected-column probes without adding production instrumentation.
#[derive(Clone)]
struct CountedRows {
    inner: SortedWritesTable,
    reads: Arc<AtomicUsize>,
}
impl Table for CountedRows {
    fn dyn_clone(&self) -> Box<dyn Table> {
        Box::new(self.clone())
    }
    fn as_any(&self) -> &dyn Any {
        self
    }
    fn spec(&self) -> TableSpec {
        self.inner.spec()
    }
    fn clear(&mut self) {
        self.inner.clear()
    }
    fn all(&self) -> Subset {
        self.inner.all()
    }
    fn len(&self) -> usize {
        self.inner.len()
    }
    fn version(&self) -> TableVersion {
        self.inner.version()
    }
    fn updates_since(&self, offset: Offset) -> Subset {
        self.inner.updates_since(offset)
    }
    fn scan_generic_bounded(
        &self,
        subset: SubsetRef,
        start: Offset,
        n: usize,
        cs: &[Constraint],
        f: impl FnMut(RowId, &[Value]),
    ) -> Option<Offset> {
        self.inner.scan_generic_bounded(subset, start, n, cs, f)
    }
    fn refine(&self, subset: Subset, cs: &[Constraint]) -> Subset {
        self.inner.refine(subset, cs)
    }
    fn get_row(&self, key: &[Value]) -> Option<Row> {
        self.reads.fetch_add(1, Ordering::Relaxed);
        self.inner.get_row(key)
    }
    fn get_row_columns(&self, key: &[Value], columns: &[ColumnId], out: &mut [Option<Value>]) {
        self.reads.fetch_add(1, Ordering::Relaxed);
        self.inner.get_row_columns(key, columns, out);
    }
    fn merge(&mut self, state: &mut ExecutionState) -> TableChange {
        self.inner.merge(state)
    }
    fn new_buffer(&self) -> Box<dyn MutationBuffer> {
        self.inner.new_buffer()
    }
}

#[test]
fn fused_lookup_reads_one_row_per_active_lane_with_independent_defaults() {
    for (direct, output_count) in [(false, 2), (false, 3), (true, 2), (true, 3)] {
        let mut db = Database::default();
        let reads = Arc::new(AtomicUsize::new(0));
        let inner =
            SortedWritesTable::new(2, 5, ColumnId::new(4), vec![], Box::new(|_, _, _, _| false));
        let table = if direct {
            db.add_table(inner, [], [])
        } else {
            db.add_table(
                CountedRows {
                    inner,
                    reads: reads.clone(),
                },
                [],
                [],
            )
        };
        db.new_buffer(table)
            .stage_insert(&[v(1), v(90), v(11), v(12), v(13)]);
        db.new_buffer(table)
            .stage_insert(&[v(5), v(90), v(51), v(52), v(53)]);
        db.merge_all();
        let input = Variable::from_usize(0);
        let fallback = Variable::from_usize(1);
        let outputs: Vec<_> = (0..output_count)
            .map(|col| LookupOutput {
                dst_col: ColumnId::from_usize(col + 2),
                dst_var: Variable::from_usize(col + 2),
                default: if col == 1 {
                    fallback.into()
                } else {
                    v(100 + col).into()
                },
            })
            .collect();
        let keys: Vec<_> = (0..8).map(v).collect();
        let defaults: Vec<_> = (0..8).map(|lane| v(200 + lane)).collect();
        let mut bindings = Bindings::new(8);
        bindings.insert(input, &keys);
        bindings.insert(fallback, &defaults);
        let pools = PoolSet::default();
        let mut mask = Mask::new(0..8, &pools);
        mask.iter(&keys).retain(|key| key.index() % 2 == 1);
        let instr = Instr::LookupColumnsWithDefaults {
            table,
            args: vec![QueryEntry::Var(input), v(90).into()],
            outputs: outputs.clone(),
        };
        db.with_execution_state(None, |state| {
            state.run_instr(&mut mask, &instr, &mut bindings)
        });
        assert_eq!(mask.ones().collect::<Vec<_>>(), [1, 3, 5, 7]);
        for (col, output) in outputs.iter().enumerate() {
            for lane in 0..8 {
                let expected = if lane % 2 == 0 {
                    Value::stale()
                } else if lane == 1 || lane == 5 {
                    v(lane * 10 + col + 1)
                } else if col == 1 {
                    defaults[lane]
                } else {
                    v(100 + col)
                };
                assert_eq!(bindings[output.dst_var][lane], expected);
            }
        }
        if !direct {
            assert_eq!(reads.load(Ordering::Relaxed), 4);
        }
    }
}
