import sys

def read_input():
    """
    Read input from the given path
    Parse formula as list(list(int))
    
    Return
    nvar: Number of propositional variables
    nclause: Number of clauses in the formula
    formula: Formula as list(list(int))
    """
    # cnf_path = sys.argv[1]
    cnf_path = 'custom_test.cnf'
    file = open(cnf_path)
    tag = 'c'
    while tag == 'c':
        tag, _, nvar, nclause = tuple(file.readline().strip().split(" "))
        nvar, nclause = int(nvar), int(nclause)

    formula = []
    for _ in range(nclause):
        clause = [int(i) for i in file.readline().strip().split(" ")[:-1]]
        formula.append(clause)
    return nvar, nclause, formula

def DPLL(nvar, nclause, formula):
    """
    Arguments
    nvar: number of propositional variables given by int
    nclause: number of clauses in formula given by int
    formula: CNF given by list(list(int))

    Return
    s_bool: Satisfiability given by bool
    v_dict: Satisfying assignment given by dict(natural number -> (bool, clause idx)) 
    e.g. 4->(true, 3) if 4 is implied assignment by clause 3
    e.g. 2->(false, None) if 2 is decision assignmnet
    """
    # Step 1 Initialize empty assignment
    s_bool = False
    v_dict = dict()
    while True:
        # Step 2 unit propagation
        simplified_formula, v_dict = unit_propagate(formula, v_dict)
        if len(simplified_formula) == 0: # Step 3
            return True, v_dict
        elif [] in formula: # Step 4 Learning Procedure
            learned_clause = clause_learning(formula, v_dict)
            formula.append(learned_clause)
            if len(learned_clause) == 0:
                return False, v_dict
            
        else:
            
    return s_bool, v_dict

def unit_propagate(formula, v_dict):
    formula = simplify(formula, v_dict)
    length_list = [len(clause) for clause in formula]
    while 1 in length_list:
        idx = length_list.index(1)
        L = formula[idx][0]
        v_dict[abs(L)] = (L > 0, idx) # Implied assignment of L to true
        formula = simplify(formula, v_dict)
        length_list = [len(clause) for clause in formula]
    return formula, v_dict

def clause_learning(formula, v_dict):
    D = formula[get_conflict_idx(formula, v_dict)]
    for p, value in v_dict.items()[::-1]:
        assign, implied = value
        if implied is None or variable_is_in_clause(p, D): # Decision assignment
            continue
        else:
            D = resolve_p(formula[implied], D, p)
    return D

def variable_is_in_clause(p, clause):
    return p in clause or -1 * p in clause

def get_conflict_idx(formula, v_dict):
    """
    Use only when conflict happens!
    """
    for i, clause in enumerate(formula):
        conflict = True
        for literal in clause:
            if eval_literal(literal, v_dict):
                conflict = False
        if conflict:
            return i
    assert False, "Use get conflict idx only when conflict happens"
    return -1

def simplify(formula, v_dict):
    """
    Simplification of formula with respect to dictionary
    - Delete literal evluated to true
    - Delete clause that contains literal evaluated to false
    """
    for i in range(len(formula))[::-1]:
        clause = formula[i]
        for j in range(len(clause))[::-1]:
            literal = clause[j]
            literal_eval = eval_literal(literal, v_dict)
            if literal_eval == 1:   # Delete clauses that contain literal evluated to true
                formula.pop(i)
            elif literal_eval == 0: # Delete literals evaluated to false
                formula[i].pop(j)
                break
    return formula

def resolve(clause1, clause2):
    """
    Resolve Two Clause
    """
    for i, elem1 in enumerate(clause1):
        for j, elem2 in enumerate(clause2):
            if elem1 == -elem2:
                clause1.pop(i)
                clause2.pop(j)
                return list(set(clause1 + clause2))
    return

def resolve_p(clause1, clause2, p):
    """
    Resolve Two Clause with p
    """
    assert((p in clause1 and -p in clause2) or (-p in clause1 and p in clause2))
    if (p in clause1 and -p in clause2):
        clause1.remove(p)
        clause2.remove(-p)
        return list(set(clause1 + clause2))
    elif (-p in clause1 and p in clause2):
        clause1.remove(-p)
        clause2.remove(p)
        return list(set(clause1 + clause2))
    assert False, "Use reolve_p only when can resolve with p"

def eval_literal(literal, v_dict):
    """
    1 if literal evaluated true by v_dict
    0 if literal evaluated false by v_dict
    -1 if literal cannot be evaluated by v_dict
    """
    key = abs(literal)
    sign = literal > 0
    if not key in v_dict:
        return -1
    elif sign:
        assign, _ = v_dict[key]
        return int(assign)
    else:
        assign, _ = v_dict[key]
        return int(not assign)

def eval_clause(clause, v_dict):
    return 1

def parse_assignment(s_bool, v_dict):
    """
    Arguments
    s_bool: Satisfiability in boolean
    v_dict: Assignment in dict(natural number -> (bool, clause idx))

    Return
    s: Satisfiability in string
    v: Assignment in desired format
    """
    v_list = [str(key) if value[0] else str(-key) for key, value in v_dict.items()]
    v = " ".join(v_list)
    s = 'SATISFIABLE' if s_bool else "UNSATISFIABLE"
    return s, v

def main():
    # Reading Input
    nvar, nclause, formula = read_input()

    # Executing DPLL
    s_bool, v_dict = DPLL(nvar, nclause, formula)

    # Parsing Output
    s, v = parse_assignment(s_bool, v_dict)
    return s, v


if __name__ == "__main__":
    formula = [[1, 3, -5], [2, -4, 3]]
    # v_dict = {1:1, 5:0, 4:1}

    print(resolve([1, 2, 4], [3, -4, 1]))
    print(simplify(formula, {1:(True, None), 4:(True, 1)}))
    # s, v = main()
    # print('s', s)
    # if s == 'SATISFIABLE':
    #     print('v', v)