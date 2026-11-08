//! An append-only [`Table`] for rows that are only appended and scanned.
//!
//! Unlike [`crate::SortedWritesTable`], this table has no keyed lookup,
//! conflict resolution, deletion, or rebuilding. Mutation buffers accumulate
//! private [`RowBuffer`] batches and submit them to a shared queue when dropped;
//! [`Table::merge`] stores immutable column chunks, keeping a batch's constant
//! columns once and avoiding copies of previously committed rows.

use std::{any::Any, sync::Arc};

use crossbeam_queue::SegQueue;

use crate::{
    TableChange,
    action::ExecutionState,
    common::Value,
    numeric_id::NumericId,
    offsets::{OffsetRange, Offsets, RowId, Subset, SubsetRef},
    row_buffer::RowBuffer,
    table_spec::{
        Constraint, Generation, MutationBuffer, Offset, Row, Table, TableSchema, TableSpec,
        TableVersion,
    },
};

#[cfg(test)]
mod tests;

struct FlatBuffer {
    rows: Option<RowBuffer>,
    pending: std::sync::Weak<SegQueue<RowBuffer>>,
}

impl MutationBuffer for FlatBuffer {
    fn stage_insert(&mut self, row: &[Value]) {
        let rows = self
            .rows
            .as_mut()
            .expect("cannot write through a dropped flat-table buffer");
        assert_eq!(
            row.len(),
            rows.arity(),
            "attempting to insert a row with the wrong arity into a FlatTable"
        );
        assert!(
            !row[0].is_stale(),
            "attempting to insert a reserved stale row into a FlatTable"
        );
        rows.add_row(row);
    }

    fn stage_remove(&mut self, _key: &[Value]) {
        panic!("FlatTable does not support removals")
    }

    fn fresh_handle(&self) -> Box<dyn MutationBuffer> {
        Box::new(Self {
            rows: Some(RowBuffer::new(
                self.rows
                    .as_ref()
                    .expect("cannot clone a dropped flat-table buffer")
                    .arity(),
            )),
            pending: self.pending.clone(),
        })
    }
}

impl Drop for FlatBuffer {
    fn drop(&mut self) {
        let Some(rows) = self.rows.take().filter(|rows| rows.len() > 0) else {
            return;
        };
        if let Some(pending) = self.pending.upgrade() {
            pending.push(rows);
        }
    }
}

#[derive(Clone)]
enum FlatColumn {
    Constant(Value),
    Values(Box<[Value]>),
}

/// A fixed-width table that supports raw appends and scans, but no keyed
/// operations.
pub struct FlatTable {
    generation: Generation,
    n_columns: usize,
    n_rows: usize,
    chunks: Vec<(RowId, Box<[FlatColumn]>)>,
    pending: Arc<SegQueue<RowBuffer>>,
}

impl Clone for FlatTable {
    fn clone(&self) -> Self {
        Self {
            generation: self.generation,
            n_columns: self.n_columns,
            n_rows: self.n_rows,
            chunks: self.chunks.clone(),
            pending: Arc::new(SegQueue::new()),
        }
    }
}

impl FlatTable {
    /// Create an empty flat table with `n_columns` physical columns.
    pub fn new(n_columns: usize) -> Self {
        assert_ne!(
            n_columns, 0,
            "attempting to create a row batch with no columns"
        );
        Self {
            generation: Generation::new(0),
            n_columns,
            n_rows: 0,
            chunks: Vec::new(),
            pending: Arc::new(SegQueue::new()),
        }
    }

    fn matches(row: &[Value], constraint: &Constraint) -> bool {
        match constraint {
            Constraint::Eq { l_col, r_col } => row[l_col.index()] == row[r_col.index()],
            Constraint::EqConst { col, val } => row[col.index()] == *val,
            Constraint::LtConst { col, val } => row[col.index()] < *val,
            Constraint::GtConst { col, val } => row[col.index()] > *val,
            Constraint::LeConst { col, val } => row[col.index()] <= *val,
            Constraint::GeConst { col, val } => row[col.index()] >= *val,
        }
    }

    fn next_row(&self) -> RowId {
        RowId::from_usize(self.n_rows)
    }

    fn row(&self, id: RowId, out: &mut [Value]) {
        let chunk = self.chunks.partition_point(|(start, _)| *start <= id) - 1;
        let (start, columns) = &self.chunks[chunk];
        let offset = id.index() - start.index();
        for (out, column) in out.iter_mut().zip(columns.iter()) {
            *out = match column {
                FlatColumn::Constant(value) => *value,
                FlatColumn::Values(values) => values[offset],
            };
        }
    }
}

impl Table for FlatTable {
    fn dyn_clone(&self) -> Box<dyn Table> {
        Box::new(self.clone())
    }

    fn as_any(&self) -> &dyn Any {
        self
    }

    fn spec(&self) -> TableSpec {
        TableSpec {
            schema: TableSchema::Flat {
                n_cols: self.n_columns,
            },
            uncacheable_columns: Default::default(),
        }
    }

    fn clear(&mut self) {
        // Isolate live buffers so a late drop cannot repopulate a cleared table.
        self.pending = Arc::new(SegQueue::new());
        if self.n_rows > 0 {
            self.chunks.clear();
            self.n_rows = 0;
            self.generation = self.generation.inc();
        }
    }

    fn all(&self) -> Subset {
        Subset::Dense(OffsetRange::new(RowId::new(0), self.next_row()))
    }

    fn len(&self) -> usize {
        self.n_rows
    }

    fn version(&self) -> TableVersion {
        TableVersion {
            major: self.generation,
            minor: Offset::from_usize(self.n_rows),
        }
    }

    fn updates_since(&self, offset: Offset) -> Subset {
        assert!(
            offset.index() <= self.n_rows,
            "update offset is newer than the FlatTable"
        );
        Subset::Dense(OffsetRange::new(
            RowId::from_usize(offset.index()),
            self.next_row(),
        ))
    }

    fn has_stale_rows(&self) -> bool {
        false
    }

    fn scan_generic_bounded(
        &self,
        subset: SubsetRef,
        start: Offset,
        n: usize,
        constraints: &[Constraint],
        mut emit: impl FnMut(RowId, &[Value]),
    ) -> Option<Offset>
    where
        Self: Sized,
    {
        let (_low, high) = subset.bounds()?;
        assert!(
            high.index() <= self.n_rows,
            "subset extends past the end of the FlatTable"
        );
        let mut row = vec![Value::new(0); self.n_columns];
        subset
            .iter_bounded(start.index(), start.index().saturating_add(n), |row_id| {
                self.row(row_id, &mut row);
                if constraints
                    .iter()
                    .all(|constraint| Self::matches(&row, constraint))
                {
                    emit(row_id, &row);
                }
            })
            .map(Offset::from_usize)
    }

    fn refine_one(&self, mut subset: Subset, constraint: &Constraint) -> Subset {
        let mut row = vec![Value::new(0); self.n_columns];
        subset.retain(|row_id| {
            self.row(row_id, &mut row);
            Self::matches(&row, constraint)
        });
        subset
    }

    fn get_row(&self, _key: &[Value]) -> Option<Row> {
        panic!("FlatTable does not support keyed lookup")
    }

    fn merge(&mut self, _exec_state: &mut ExecutionState) -> TableChange {
        let mut submitted = Vec::new();
        while let Some(rows) = self.pending.pop() {
            submitted.push(rows);
        }
        if submitted.is_empty() {
            return TableChange { added: false };
        }

        let added = submitted
            .iter()
            .try_fold(0usize, |count, rows| count.checked_add(rows.len()))
            .expect("FlatTable pending row count overflow");
        let final_len = self
            .n_rows
            .checked_add(added)
            .expect("FlatTable row count overflow");
        // Validate that the dense subset endpoint remains representable.
        RowId::from_usize(final_len);

        for rows in submitted {
            let start = self.next_row();
            self.n_rows += rows.len();
            let first = rows.get_row(RowId::new(0));
            let columns = (0..self.n_columns)
                .map(|col| {
                    if rows.iter().all(|row| row[col] == first[col]) {
                        FlatColumn::Constant(first[col])
                    } else {
                        FlatColumn::Values(rows.iter().map(|row| row[col]).collect())
                    }
                })
                .collect();
            self.chunks.push((start, columns));
        }

        TableChange { added: added > 0 }
    }

    fn new_buffer(&self) -> Box<dyn MutationBuffer> {
        Box::new(FlatBuffer {
            rows: Some(RowBuffer::new(self.n_columns)),
            pending: Arc::downgrade(&self.pending),
        })
    }
}
