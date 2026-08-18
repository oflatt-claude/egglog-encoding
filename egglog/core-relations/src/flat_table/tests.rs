use std::panic::{AssertUnwindSafe, catch_unwind};

use crate::{
    FlatTable, Table, Value,
    numeric_id::NumericId,
    offsets::SubsetRef,
    table_shortcuts::v,
    table_spec::{ColumnId, Constraint, Offset, WrappedTable},
};

fn stage<const N: usize>(table: &WrappedTable, rows: &[[Value; N]]) {
    let mut buffer = table.new_buffer();
    for row in rows {
        buffer.stage_insert(row);
    }
}

fn scan(table: &WrappedTable, subset: SubsetRef<'_>) -> Vec<Vec<Value>> {
    table
        .scan(subset)
        .iter()
        .map(|(_, row)| row.to_vec())
        .collect()
}

fn sorted_rows(table: &WrappedTable) -> Vec<Vec<Value>> {
    let mut rows = scan(table, table.all().as_ref());
    rows.sort_unstable();
    rows
}

#[test]
fn appends_preserve_rows_duplicates_and_deltas() {
    empty_execution_state!(exec_state);
    let mut table = WrappedTable::new(FlatTable::new(3));

    let spec = table.spec();
    assert_eq!(spec.n_keys, 3);
    assert_eq!(spec.n_vals, 0);
    assert!(!spec.allows_delete);
    assert!(!table.has_stale_rows());

    stage(&table, &[[v(1), v(2), v(3)], [v(1), v(2), v(3)]]);
    assert!(table.is_empty(), "staged rows stay hidden until merge");
    assert!(table.merge(&mut exec_state).added);
    assert_eq!(
        scan(&table, table.all().as_ref()),
        vec![vec![v(1), v(2), v(3)], vec![v(1), v(2), v(3)],]
    );

    let before = table.version();
    stage(&table, &[[v(4), v(5), v(6)]]);
    assert!(table.merge(&mut exec_state).added);
    assert_eq!(
        scan(&table, table.updates_since(before.minor).as_ref()),
        vec![vec![v(4), v(5), v(6)]]
    );
    assert!(!table.merge(&mut exec_state).added);
}

#[test]
fn scans_apply_constraints_without_keyed_lookup() {
    empty_execution_state!(exec_state);
    let mut table = WrappedTable::new(FlatTable::new(3));
    stage(
        &table,
        &[
            [v(1), v(1), v(10)],
            [v(1), v(2), v(20)],
            [v(2), v(3), v(30)],
        ],
    );
    table.merge(&mut exec_state);

    let matching = table.refine(
        table.all(),
        &[
            Constraint::GeConst {
                col: ColumnId::new(1),
                val: v(2),
            },
            Constraint::LtConst {
                col: ColumnId::new(2),
                val: v(30),
            },
        ],
    );
    assert_eq!(
        scan(&table, matching.as_ref()),
        vec![vec![v(1), v(2), v(20)]]
    );

    let lookup = catch_unwind(AssertUnwindSafe(|| table.get_row(&[v(1), v(2)])));
    assert!(
        lookup.is_err(),
        "flat tables must not grow a lookup contract"
    );
}

#[test]
fn clear_discards_submitted_and_late_batches() {
    empty_execution_state!(exec_state);
    let mut table = WrappedTable::new(FlatTable::new(2));
    stage(&table, &[[v(0), v(0)]]);
    table.merge(&mut exec_state);

    stage(&table, &[[v(1), v(1)]]);
    let mut late = table.new_buffer();
    late.stage_insert(&[v(2), v(2)]);
    let version = table.version();
    table.clear();
    drop(late);

    assert!(table.is_empty());
    assert_eq!(table.version().major, version.major.inc());
    assert_eq!(table.version().minor, Offset::new(0));
    assert!(!table.merge(&mut exec_state).added);
}

#[test]
fn clone_owns_an_independent_pending_snapshot() {
    empty_execution_state!(exec_state);
    let mut original = WrappedTable::new(FlatTable::new(2));
    stage(&original, &[[v(0), v(0)]]);
    original.merge(&mut exec_state);
    stage(&original, &[[v(1), v(1)]]);

    let mut cloned = original.dyn_clone();
    stage(&original, &[[v(2), v(2)]]);
    stage(&cloned, &[[v(3), v(3)]]);

    original.merge(&mut exec_state);
    cloned.merge(&mut exec_state);
    assert_eq!(
        sorted_rows(&original),
        vec![vec![v(0), v(0)], vec![v(1), v(1)], vec![v(2), v(2)]]
    );
    assert_eq!(
        sorted_rows(&cloned),
        vec![vec![v(0), v(0)], vec![v(1), v(1)], vec![v(3), v(3)]]
    );
}

#[test]
fn concurrent_clones_see_the_same_pending_snapshot() {
    empty_execution_state!(exec_state);
    let original = WrappedTable::new(FlatTable::new(2));
    stage(&original, &[[v(1), v(1)], [v(2), v(2)]]);

    let (mut left, mut right) = std::thread::scope(|scope| {
        let left = scope.spawn(|| original.dyn_clone());
        let right = scope.spawn(|| original.dyn_clone());
        (left.join().unwrap(), right.join().unwrap())
    });
    left.merge(&mut exec_state);
    right.merge(&mut exec_state);

    assert_eq!(sorted_rows(&left), sorted_rows(&right));
    assert_eq!(left.len(), 2);
}

#[test]
fn parallel_batches_are_appended_without_loss() {
    empty_execution_state!(exec_state);
    let mut table = WrappedTable::new(FlatTable::new(2));
    let batches = 64;
    let rows_per_batch = 128;

    std::thread::scope(|scope| {
        for batch in 0..batches {
            let table = &table;
            scope.spawn(move || {
                let mut buffer = table.new_buffer();
                for row in 0..rows_per_batch {
                    let id = batch * rows_per_batch + row;
                    buffer.stage_insert(&[v(id), v(batch)]);
                }
            });
        }
    });
    let pool = egglog_concurrency::ThreadPool::new(4);
    pool.install(|| table.merge(&mut exec_state));

    assert_eq!(table.len(), batches * rows_per_batch);
    let rows = sorted_rows(&table);
    assert_eq!(rows.first(), Some(&vec![v(0), v(0)]));
    assert_eq!(
        rows.last(),
        Some(&vec![v(batches * rows_per_batch - 1), v(batches - 1)])
    );
}

#[test]
fn removals_wrong_arity_and_stale_rows_are_rejected() {
    let table = FlatTable::new(2);
    assert!(
        catch_unwind(AssertUnwindSafe(|| {
            table.new_buffer().stage_remove(&[v(1)])
        }))
        .is_err()
    );
    assert!(
        catch_unwind(AssertUnwindSafe(|| {
            table.new_buffer().stage_insert(&[v(1)])
        }))
        .is_err()
    );
    assert!(
        catch_unwind(AssertUnwindSafe(|| {
            table.new_buffer().stage_insert(&[Value::stale(), v(1)])
        }))
        .is_err()
    );
}
