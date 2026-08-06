#!/usr/bin/python3 -B

# remaining issues:
# - non-projective applier patterns
# - symmetries
# - redundancies (for later)

type SExpr = tuple[SExpr, ...] | str

def parse(s: str) -> SExpr:
    s = s.replace("\n", " ").replace("\t", " ").replace("(", " ( ").replace(")", " ) ")
    toks = [tok for tok in s.split(" ") if tok != ""]
    for i in range(len(toks))[::-1]:
        if toks[i] == "(":
            j = i
            while toks[j] != ")":
                j += 1
            new = tuple(toks[i+1:j])
            toks = toks[:i] + [new] + toks[j+1:]
    assert(len(toks) == 1)
    return toks[0]

def proplist_to_sexpr(l):
    rename = l[0]
    for xx in l[1:]:
        rename = ("compose", rename, xx)
    return rename

def transform_rhs(e, varmap): # returns GId
    if e == "Null": return "identity", "Null"
    elif len(e) == 3 and e[0] == "App1":
        g2, e2 = transform_rhs(e[2], varmap)
        return "identity", ("App1", e[1], g2, e2)
    elif len(e) == 4 and e[0] == "App2":
        g2, e2 = transform_rhs(e[2], varmap)
        g3, e3 = transform_rhs(e[3], varmap)
        return "identity", ("App2", e[1], g2, e2, g3, e3)
    elif len(e) == 1 and type(v := e[0]) == str:
        return proplist_to_sexpr(varmap[v][0]), f"{v}_l"
    else:
        print(f"what is {e}?")
        raise "oh no"

def transform_rewrite(rw):
    assert(rw[0] == "rewrite")
    assert(len(rw) == 3)
    lhs = rw[1]
    rhs = rw[2]

    lhs = stage1(lhs, [0], [], varmap := {})
    g, new_rhs = transform_rhs(rhs, varmap)

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

    outs.append(("RenamesToLeader", "this", "identity", "this"))
    outs.append(("=", "identity", ("compose", "identity", "identity")))
        
    return ("rule", tuple(outs), (("Union", "this", g, new_rhs),))

# varmap["x"] = ["m1*m2", "m2*m3", ...]
def stage1(e, ctr, prop, varmap):
    if e == "Null": return "Null"
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
        print(f"what is {e}?")
        raise "oh no"

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

import sys
filename = sys.argv[1]
content = open(filename).read()

parsed = parse(content)
compiled = transform_rewrite(parsed)
print(pretty_print(compiled))
