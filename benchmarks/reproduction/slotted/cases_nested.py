"""Nested/aliasing cases from the retired differential runner."""

CASES = [
    ("optional", "(union (G $0 (Null)) (Null))", "(F $1 (Null))", "(F a (G b n))", "(H a b)", True),
    ("repeated-var", "(union (G $0 (Null)) (Null))", "(F $1 (Null))", "(F a (G a n))", "(H a a)", True),
    ("repeated-literal", "(union (G $0 (Null)) (Null))", "(F $1 (Null))", "(F $x (G $x n))", "(H $x $x)", True),
    (
        "siblings",
        "(union (G $0 (Null)) (Null)) (union (K $1 (Null)) (Null))",
        "(F (Null) (Null))",
        "(F (G a n) (K b m))",
        "(H a b)",
        True,
    ),
    (
        "sibling-repeat",
        "(union (G $0 (Null)) (Null)) (union (K $1 (Null)) (Null))",
        "(F (Null) (Null))",
        "(F (G a n) (K a m))",
        "(H a a)",
        True,
    ),
    ("shared", "", "(F $0 (G $0 (Null)))", "(F a (G a n))", "(H a a)", False),
    ("binders", "", "(F (Lam $0 $0) (Lam $1 $1))", "(F (Lam $x a) (Lam $x b))", "(H a b)", True),
    ("named-binders", "", "(F (Lam $a $a) (Lam $a0 $a0))", "(F (Lam $x a) (Lam $x b))", "(H a b)", True),
    ("named-and-numbered", "", "(F $a0 (G $0 (Null)))", "(F a (G b n))", "(H a b)", False),
    (
        "named-shadowing",
        "",
        "(Lam $a (Lam $a (F $a $a0)))",
        "(Lam $x (Lam $y (F $y body)))",
        "(Lam $x (Lam $y (G body $y)))",
        False,
    ),
    ("binder-capture", "", "(F $4 (Lam $5 $5))", "(F a (Lam $x b))", "(Lam $x (F a b))", True),
    (
        "symmetry",
        "(union (F $0 $1) (F $1 $0))",
        "(G $0 (F $0 $1))",
        "(G $x (F a $x))",
        "(H a $x)",
        False,
    ),
]
