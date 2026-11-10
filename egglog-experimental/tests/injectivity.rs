//! Separate injectivity: cancellation and upward disequality with fixed other inputs.
use egglog::EGraph;
use egglog_experimental::{
    new_experimental_egraph_for_proofs, new_experimental_egraph_with_proof_testing,
    new_experimental_egraph_with_term_encoding,
};

const MODES: [fn() -> EGraph; 3] = [
    new_experimental_egraph_for_proofs,
    new_experimental_egraph_with_term_encoding,
    new_experimental_egraph_with_proof_testing,
];

#[test]
fn each_coordinate_cancels_only_with_the_other_inputs_fixed() {
    for mode in MODES {
        mode()
            .parse_and_run_program(
                None,
                "
            (datatype T (A) (B) (C) (D) (Pair T T) (Plain T T))
            (separately-injective Pair)
            (union (Pair (A) (C)) (Pair (B) (D)))
            (fail (check (= (A) (B)))) (fail (check (= (C) (D))))
            (union (Pair (A) (A)) (Pair (A) (B)))
            (check (= (A) (B)))
            (union (Pair (C) (A)) (Pair (D) (A)))
            (check (= (C) (D)))
            (union (Plain (A) (A)) (Plain (C) (A)))
            (fail (check (= (A) (C))))
        ",
            )
            .unwrap();
    }
}

#[test]
fn native_coordinates_seed_disequality_and_detect_guarded_contradictions() {
    for mode in MODES {
        mode()
            .parse_and_run_program(
                None,
                "
            (datatype T (A) (B) (Mixed T i64))
            (separately-injective Mixed)
            (Mixed (A) 1) (Mixed (A) 2) (Mixed (B) 3)
            (check (known-disequal (Mixed (A) 1) (Mixed (A) 2)))
            (fail (check (known-disequal (Mixed (A) 1) (Mixed (B) 3))))
            (union (Mixed (A) 1) (Mixed (B) 3))
            (fail (check (contradiction)))
            (union (Mixed (A) 1) (Mixed (A) 2))
            (check (contradiction))
        ",
            )
            .unwrap();
    }
}

#[test]
fn unary_cancellation_includes_subsumed_rows_and_recursive_layers() {
    for mode in MODES {
        mode()
            .parse_and_run_program(
                None,
                "
            (datatype T (A) (B) (Wrap T))
            (separately-injective Wrap)
            (let x (Wrap (Wrap (A)))) (let y (Wrap (Wrap (B))))
            (subsume (Wrap (Wrap (A))))
            (union x y)
            (check (= (A) (B)))
        ",
            )
            .unwrap();
    }
}

#[test]
fn markings_follow_scope_clone_and_fresh_proof_identities() {
    for mode in MODES {
        let mut graph = mode();
        graph
            .parse_and_run_program(
                None,
                "
            (datatype T (A) (B) (Wrap T))
            (push) (separately-injective Wrap)
            (union (Wrap (A)) (Wrap (B))) (check (= (A) (B)))
            (pop)
            (union (Wrap (A)) (Wrap (B))) (fail (check (= (A) (B))))
        ",
            )
            .unwrap();
        let mut clone = graph.clone();
        clone
            .parse_and_run_program(None, "(separately-injective Wrap) (check (= (A) (B)))")
            .unwrap();
        graph
            .parse_and_run_program(
                None,
                "(fail (check (= (A) (B)))) (separately-injective Wrap) (check (= (A) (B)))",
            )
            .unwrap();
    }
}

#[test]
fn markings_require_one_existing_ordinary_constructor_and_supported_sorts() {
    for mode in MODES {
        let mut graph = mode();
        graph
            .run_program(vec![egglog::ast::Command::Sort {
                span: egglog::span!(),
                name: "Token".into(),
                presort_and_args: None,
                uf: None,
                container_rebuild: None,
                proof_constructors: None,
                unionable: false,
            }])
            .unwrap();
        graph
            .parse_and_run_program(
                None,
                "
            (datatype T (A) (F T)) (function plain (T) i64 :merge new)
            (sort Items (Vec T)) (constructor Container (Items) T)
            (constructor Nonunion (T) Token)
            (constructor Input (Token) T)
            (constructor Internal (T) T :internal-role global)
            (separately-injective A)
        ",
            )
            .unwrap();
        for source in [
            "(separately-injective)",
            "(separately-injective F A)",
            "(separately-injective (F))",
            "(separately-injective Missing)",
            "(separately-injective plain)",
            "(separately-injective Container)",
            "(separately-injective Nonunion)",
            "(separately-injective Input)",
            "(separately-injective Internal)",
            "(constructor Old (T) T :injective)",
            "(datatype Old (OldNode T :injective))",
        ] {
            assert!(
                graph.parse_and_run_program(None, source).is_err(),
                "{source}"
            );
        }
        graph
            .parse_and_run_program(
                None,
                "(union (F (A)) (F (F (A)))) (fail (check (= (A) (F (A)))))",
            )
            .unwrap();
    }
}

#[test]
fn mutual_datatypes_and_dynamic_cost_declarations_need_no_special_annotation_plumbing() {
    for mode in MODES {
        mode()
            .parse_and_run_program(
                None,
                "
            (datatype* (Expr (A) (B) (Block Stmt)) (Stmt (Return Expr i64)))
            (separately-injective Block) (separately-injective Return)
            (union (Block (Return (A) 0)) (Block (Return (B) 0)))
            (check (= (A) (B)))
        ",
            )
            .unwrap();
    }
}
