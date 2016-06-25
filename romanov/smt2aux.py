def parse_sexp(smt2):
    # parser S-expression as recurive list
    toks = smt2.replace('(', ' ( ').replace(')', ' ) ').split()
    stack = [[]]
    for tok in toks:
        if tok == '(':
            stack.append([])
            continue
        if tok == ')':
            tok = stack.pop()
        stack[-1].append(tok)
    return stack[0]

def sexp_to_int(value):
    if value == 'true':
        return 1, 1

    if value == 'false':
        return 0, 1

    try:
        assert value.startswith('#x')
        # remove #x prefix
        value = value[2:]
        bits = 4 * len(value)
        ivalue = int(value, 16)
        return ivalue, bits
    except: pass

    try:
        assert value.startswith('#b')
        # remove #b prefix
        value = value[2:]
        bits = len(value)
        ivalue = int(value, 2)
        return ivalue, bits
    except: pass

    try:
        assert isinstance(value, list)
        assert len(value) == 3
        assert value[0] == '_'
        assert value[1].startswith('bv')
        ivalue = int(value[1][2:])
        bits = int(value[2])
        return ivalue, bits
    except: pass

    raise ValueError('not a valid S-expression integer')

def smt2_to_int(smt2):
    "Parse SMTLIB2 answer to (get-value) into Python int"
    sexp = parse_sexp(smt2)
    print(sexp)

    assert len(sexp) == 1, "single s-expression expected"
    sexp = sexp[0]
    assert len(sexp) == 1, "single s-expression at level 2 expected"
    sexp = sexp[0]
    assert len(sexp) == 2, "2-tuple expected at level 3"
    label = sexp[0]
    ivalue, bits = sexp_to_int(sexp[1])
    if ivalue >= 2**(bits - 1):
        ivalue -= 2**bits
    return ivalue
