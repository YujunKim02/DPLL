import sys

def read_input(cnf_path):
    """
    Read input from the given path
    Parse formula as list(list(int))
    
    Return
    nvar: Number of propositional variables
    nclause: Number of clauses in the formula
    formula: Formula as list(list(int))
    """
    
    file = open(cnf_path)
    tag = 'c'
    while tag == 'c':
        line = file.readline().strip().split(" ")
        tag = line[0]
        if tag == 'p':
            nvar, nclause = int(line[2]), int(line[3])

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
    v_order = []
    num_iter = 0
    while True:
        num_iter += 1
        # Step 2 unit propagation
        copied_formula_for_unit_propagate = [clause[:] for clause in formula]
        copied_formula_for_simplify = [clause[:] for clause in formula]
        v_dict, v_order = unit_propagate(copied_formula_for_unit_propagate, v_dict, v_order)
        simplified_formula = simplify(copied_formula_for_simplify, v_dict)
        if len(simplified_formula) == 0: # Step 3
            return True, v_dict, num_iter
        elif [] in simplified_formula: # Step 4 Clause learning Procedure
            copied_formula_for_clause_learning = [clause[:] for clause in formula]
            learned_clause = clause_learning(copied_formula_for_clause_learning, v_dict, v_order)
            formula.append(learned_clause)
            if len(learned_clause) == 0:
                return False, v_dict, num_iter
            else:
                # Backtrack
                v_dict, v_order = backtrack(v_dict, v_order, learned_clause)
        else:
            # Step 5 Decision Strategy
            v_dict, v_order = dumb_decision_strategy(nvar, v_dict, v_order)
    return s_bool, v_dict, num_iter

def backtrack(v_dict, v_order, learned_clause):
    while len(v_order) and not is_unit(learned_clause, v_dict):
        idx = v_order.pop()
        v_dict.pop(idx)
    return v_dict, v_order

def is_unit(clause, v_dict):
    clause_eval = [eval_literal(literal, v_dict) for literal in clause]
    return clause_eval.count(-1) == 1

def unit_propagate(formula, v_dict, v_order):
    formula = simplify_without_deleting_clause(formula, v_dict)
    length_list = [len(clause) for clause in formula]
    while 1 in length_list:
        idx = length_list.index(1)
        L = formula[idx][0]
        v_dict[abs(L)] = (L > 0, idx) # Implied assignment of L to true
        v_order.append(abs(L))
        formula = simplify_without_deleting_clause(formula, v_dict)
        length_list = [len(clause) for clause in formula]
    return v_dict, v_order

def clause_learning(formula, v_dict, v_order):
    # print(f'clause learning with formula: {formula}, v_dict: {v_dict}, v_order: {v_order}')
    D = formula[get_conflict_idx(formula, v_dict)]
    for p in v_order[::-1]:
        value = v_dict[p]
        assign, implied = value
        if implied is None or not variable_is_in_clause(p, D): # Decision assignment
            continue
        else:
            D = resolve_p(formula[implied], D, p)
    # print(f"learned {D}")
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
                break
            elif literal_eval == 0: # Delete literals evaluated to false
                formula[i].pop(j)
    return formula

def simplify_without_deleting_clause(formula, v_dict):
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
            if literal_eval == 1:   # Empty the clauses that contain literal evluated to true
                formula[i] = []
                break
            if literal_eval == 0: # Delete literals evaluated to false
                formula[i].pop(j)
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

def dumb_decision_strategy(nvar, v_dict, v_order):
    """
    Assign true to first undecided variable
    """
    for i in range(1, nvar + 1):
        try:
            v_dict[i]
        except KeyError:
            v_dict[i] = (True, None)
            v_order.append(i)
            return v_dict, v_order
    assert False, "All variables already assigned"

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
    """
    Evaluate a clause with respect to v_dict
    Return True if clause is satisfied, False otherwise
    """
    for literal in clause:
        if eval_literal(literal, v_dict) == 1:
            return True
    return False

def eval_formula(formula, v_dict):
    """
    Evaluate a formula with respect to v_dict
    Return True if clause is satisfied, False otherwise
    """
    for clause in formula:
        if eval_clause(clause, v_dict) == False:
            return False
    return True

def parse_assignment(s_bool, v_dict):
    """
    Arguments
    s_bool: Satisfiability in boolean
    v_dict: Assignment in dict(natural number -> (bool, clause idx))

    Return
    s: Satisfiability in string
    v: Assignment in desired format
    """
    sorted_key = sorted(v_dict.keys())
    v_list = [str(key) if v_dict[key][0] else str(-key) for key in sorted_key]
    v = " ".join(v_list)
    s = 'SATISFIABLE' if s_bool else "UNSATISFIABLE"
    return s, v

def main():
    # Reading Input
    cnf_path = sys.argv[1]
    nvar, nclause, formula = read_input(cnf_path)
    copied_formula_for_validity = [clause[:] for clause in formula]
    # Executing DPLL
    s_bool, v_dict, num_iter = DPLL(nvar, nclause, formula)
    if s_bool:
        evaluated = eval_formula(copied_formula_for_validity, v_dict)
        # assert(evaluated)

    # Parsing Output
    s, v = parse_assignment(s_bool, v_dict)
    # print(f'num_var: {nvar}, num_iter: {num_iter}')
    print('s', s)
    if s == 'SATISFIABLE':
        print('v', v, 0)


if __name__ == "__main__":
    # formula = [[1, 3, -5], [2, -4, 3]]
    # v_dict = {1:1, 5:0, 4:1}

    # print(resolve([1, 2, 4], [3, -4, 1]))
    # formula = [[1, -1], [1, 3], [-1, -3], [2, 3]]
    # print(simplify(formula, {1:(True, None), 4:(True, 1)}))
    
    main()