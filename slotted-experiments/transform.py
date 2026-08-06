#!/usr/bin/python3 -B

# remaining issues:
# - symmetries
# - redundancies (for later)

import sys

type SExpr = tuple[SExpr, ...] | str

def parse(s: str) -> [SExpr]:
    s = s.replace("\n", " ").replace("\t", " ").replace("(", " ( ").replace(")", " ) ")
    toks = [tok for tok in s.split(" ") if tok != ""]
    for i in range(len(toks))[::-1]:
        if toks[i] == "(":
            j = i
            while toks[j] != ")":
                j += 1
            new = tuple(toks[i+1:j])
            toks = toks[:i] + [new] + toks[j+1:]
    return toks

def find_vars(x, s):
    if type(x) == str:
        try:
            int(x)
            s.add(x)
        except: pass
    elif type(x) in [tuple, list]:
        for xx in x:
            find_vars(xx, s)
    else:
        crash(f"what is {x}?")

def crash(x):
    print(x, file=sys.stderr)
    exit(1)

def proplist_to_sexpr(l):
    rename = l[0]
    for xx in l[1:]:
        rename = ("compose", rename, xx)
    return rename

def transform_rule(rule):
    if rule[0] == "rewrite":
        return [transform_rewrite(rule)]
    elif rule[0] == "let":
        var = rule[1]
        g, val = transform_rhs(rule[2], {})
        constr = f"{var}_constr"
        c_def = ("constructor", constr, "()", "U")
        let_def = ("let", var, (constr,))
        relate = ("Union", var, g, val)
        return [c_def, let_def, relate]
    elif rule[0] == "run":
        return [rule]
    elif rule[0] == "check":
        return [rule]
    else:
        crash(f"transform_rule: unknown rule type {rule}")

def transform_rhs(e, varmap): # returns GId
    if e == ("Null",): return "$global_identity", ("Null",)
    elif len(e) == 2 and e[0] == "Var":
        return ("map-insert", ("map-empty",), "0", e[1]), ("Var", "0")
    elif len(e) == 3 and e[0] == "App1":
        g2, e2 = transform_rhs(e[2], varmap)
        return "$global_identity", ("App1", e[1], g2, e2)
    elif len(e) == 4 and e[0] == "App2":
        g2, e2 = transform_rhs(e[2], varmap)
        g3, e3 = transform_rhs(e[3], varmap)
        return "$global_identity", ("App2", e[1], g2, e2, g3, e3)
    elif len(e) == 1 and type(v := e[0]) == str:
        return proplist_to_sexpr(varmap[v][0]), f"{v}_l"
    else:
        crash(f"transform_rhs: what is {e}?")

def transform_searcher(lhs):
    lhs = stage1(lhs, [0], [], varmap := {})

    outs = []
    outs.append(("=", "this", lhs))
    for v, ll in varmap.items():
        canon = ll[0]
        for l in ll[1:]:
            a1 = proplist_to_sexpr(canon)
            a2 = proplist_to_sexpr(l)
            # we wanna state a1*v_l = a2*v_l -> a1-¹*a2 is a symmetry
            sym = ("compose", ("inverse", a1), a2)
            vl = v + "_l"
            c = ("RenamesToLeader", vl, sym, vl)
            outs.append(c)

    return outs, varmap

def transform_rewrite(rw):
    assert(rw[0] == "rewrite")
    assert(len(rw) == 3)
    lhs = rw[1]
    rhs = rw[2]

    outs, varmap = transform_searcher(lhs)
    g, new_rhs = transform_rhs(rhs, varmap)
        
    return ("rule", tuple(outs), (("Union", "this", g, new_rhs),))

# varmap["x"] = ["m1*m2", "m2*m3", ...]
def stage1(e, ctr, prop, varmap):
    if e == ("Null",): return ("Null",)
    elif len(e) == 3 and e[0] == "App1":
        c = ctr[0]
        ctr[0] += 1

        m = f"m_{c}"
        e2 = stage1(e[2], ctr, prop + [m], varmap)
        return ("App1", e[1], m, e2)
    elif len(e) == 4 and e[0] == "App2":
        c1 = ctr[0]
        ctr[0] += 1

        c2 = ctr[0]
        ctr[0] += 1

        m1 = f"m_{c1}"
        m2 = f"m_{c2}"
        e2 = stage1(e[2], ctr, prop + [m1], varmap)
        e3 = stage1(e[3], ctr, prop + [m2], varmap)
        return ("App2", e[1], m1, e2, m2, e3)
    elif len(e) == 1 and type(v := e[0]) == str:
        if v not in varmap: varmap[v] = []
        n = len(varmap[v])
        varmap[v].append(prop)
        return f"{v}_l"
    else:
        crash(f"stage1: what is {e}?")

def size(e):
    if isinstance(e, str): return 1
    return sum(size(x) for x in e)

def base_pretty_print(expr):
    if isinstance(expr, str): return expr
    return "(" + " ".join([base_pretty_print(x) for x in expr]) + ")"

def pretty_print(expr: SExpr, indent=0):
    if size(expr) < 10: return base_pretty_print(expr)
    
    new_indent = indent + 2
    spacing = " " * new_indent
    head = pretty_print(expr[0], new_indent)
    tail = f"\n{spacing}".join(pretty_print(x, new_indent) for x in expr[1:])
    
    return f"({head}\n{spacing}{tail})"

def define_global_identity(parsed):
    find_vars(parsed, s := set())
    d = ("map-empty",)
    for x in s:
        d = ("map-insert", d, x, x)

    print(pretty_print(("let", "$global_identity", d)))

import sys
filename = sys.argv[1]
content = open(filename).read()

parsed = parse(content)
define_global_identity(parsed)

for x in parsed:
    for x in transform_rule(x):
        print(pretty_print(x))
