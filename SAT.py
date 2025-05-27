from strategies import *
from functions import *
import time


start = time.time()

def read_clauses_from_file(filename):
    clauses = set()
    nr_var=0
    nr_clauses=0
    with open(filename, 'r') as f:
        for line in f:
            line = line.strip().split()
            if not line:
                continue  # Skip empty lines
            else:
                literals = [int(x) for x in line if int(x)!=0]  # ignore all zeros
                clause = frozenset(literals)
                clauses.add(clause)
                nr_clauses += 1
                nr_var = max(nr_var, max(abs(lit) for lit in literals))
    return nr_var, nr_clauses, clauses

file_name="./clauses/cnf_8"
nr_var, nr_clauses, clauses = read_clauses_from_file(file_name)

print(f"Number of variables: {nr_var}")
print(f"Number of clauses: {nr_clauses}")


def resolution(clauses, msg=True):
    start_time = time.time()
    clauses = [frozenset(c) for c in clauses]
    nr = 1
    if msg:
        print("Initial clauses:")
    displayed_clauses = set()  # Track displayed clauses
    for _, clause in enumerate(clauses):
        clause_str = format_clause(clause)
        if clause_str not in displayed_clauses:
            if msg:
                print(f"({nr}) {clause_str}")
                nr += 1
            displayed_clauses.add(clause_str)
    if msg:
        print("-" * 60)

    new = set()
    resolved_pairs = set()
    clause_set = set(clauses)

    while True:
        n = len(clauses)
        for i in range(n):
            for j in range(i + 1, n):
                ci, cj = clauses[i], clauses[j]
                if (ci, cj) in resolved_pairs or (cj, ci) in resolved_pairs:
                    continue
                resolved_pairs.add((ci, cj))
                resolvents = resolve(ci, cj)
                for resolvent in resolvents:
                    resolvent_str = format_clause(resolvent)
                    if resolvent_str not in displayed_clauses:
                        if msg:
                            print(f"({nr}) {resolvent_str} from {format_clause(set(ci))} and {format_clause(set(cj))}")
                        displayed_clauses.add(resolvent_str)
                        nr += 1
                    if not resolvent:
                        if msg:
                            print("\n  ∅ generated. UNSATISFIABLE")
                        else:
                            print("The formula is UNSATISFIABLE")
                        print("Time measurement: ", time.time() - start_time)
                        return True
                    new.add(resolvent)

        if new.issubset(clauses):
            if msg:
                print("\nNo new clauses generated")
            print("The formula is SATISFIABLE")
            print("Time measurement: ", time.time() - start_time)
            return False

        for c in new:
            if c not in clauses:
                clauses.append(c)
                clause_set.add(c)



'''
def davis_putnam(clauses, msg=True):
    #Apply the Davis-Putnam procedure to solve the SAT problem.
    start_time=time.time()
    if msg:
        print("Initial clauses:")
        for i, clause in enumerate(clauses, 1):
            print(f"({i}) {format_clause(clause)}")
        print("-" * 60)

    # Apply unit propagation
    clauses = apply_unit_propagation(clauses, msg=msg)
    if clauses is False:
        print("The formula is UNSATISFIABLE")
        print("Time measurement: ", time.time() - start_time)
        return False  # A contradiction was found

    # Apply pure literal rule
    clauses = apply_pure_literal_rule(clauses, msg=msg)
    if not clauses:
        print("The formula is SATISFIABLE")
        print("Time measurement: ", time.time() - start_time)
        return True  # Formula is satisfiable

    if msg:
        print("\nNeither unit propagation nor pure literal rule can be applied. Now performing resolution...")

    # Perform resolution if neither unit propagation nor pure literal rule worked
    return resolution(clauses, msg=msg)
'''

def davis_putnam(clauses, msg=True):
    # Apply the Davis-Putnam procedure to solve the SAT problem.
    import time
    start_time = time.time()

    if msg:
        print("Initial clauses:")
        for i, clause in enumerate(clauses, 1):
            print(f"({i}) {format_clause(clause)}")
        print("-" * 60)

    while True:
        # Apply unit propagation
        updated_clauses = apply_unit_propagation(clauses, msg=msg)
        if updated_clauses is False:
            print("The formula is UNSATISFIABLE")
            print("Time measurement: ", time.time() - start_time)
            return False
        if updated_clauses != clauses:
            clauses = updated_clauses
            continue  # Try again from the top

        # Apply pure literal rule
        updated_clauses = apply_pure_literal_rule(clauses, msg=msg)
        if updated_clauses != clauses:
            if not updated_clauses:
                print("The formula is SATISFIABLE")
                print("Time measurement: ", time.time() - start_time)
                return True
            clauses = updated_clauses
            continue  # Try again from the top

        # If neither rule applies, perform resolution
        if msg:
            print("\nNeither unit propagation nor pure literal rule can be applied. Now performing resolution...")

        result = resolution(clauses, msg=msg)
        if result:
            # If resolution returns True, that means ∅ (empty clause) was derived
            # → the formula is UNSATISFIABLE
            return False
        else:
            # If resolution returns False, that means no contradiction was found
            # → the formula is SATISFIABLE
            return True


# DPLL Algorithm with Splitting
def dpll(clauses, splitting_strategy="first", depth=0, msg=True, nr_splits=0):
    #DPLL Algorithm with different splitting strategies.

    start_time=time.time()

    indentation = " " * depth

    # Apply Unit Propagation (One-Literal Rule)
    clauses = apply_unit_propagation(clauses, depth, msg=msg)
    if clauses is False:
        if depth > 1 and msg:
            print(f"{indentation}Conflict found. Backtracking...")
        return False, nr_splits  # Conflict found
    if not clauses:
        if depth > 1 and msg:
            print(f"{indentation}All clauses satisfied.")
        return True, nr_splits  # All clauses satisfied (no remaining clauses)

    # Apply Pure Literal Rule
    clauses = apply_pure_literal_rule(clauses, depth, msg=msg)
    if not clauses:
        return True, nr_splits  # All clauses satisfied (no remaining clauses)

    # Choose a literal for splitting based on the selected strategy
    if splitting_strategy == "random":
        literal = choose_literal_random(clauses)
    elif splitting_strategy == "first":
        literal = choose_literal_first(clauses)
    elif splitting_strategy == "most_frequent":
        literal = choose_literal_most_frequent(clauses)
    elif splitting_strategy == "MOMS":
        literal = choose_literal_MOMS(clauses)
    elif splitting_strategy == "MAMS":
        literal = choose_literal_MAMS(clauses)
    elif splitting_strategy == "JW":
        literal = choose_literal_JW(clauses)
    elif splitting_strategy == "DLCS":
        literal = choose_literal_DLCS(clauses)
    else:
        raise ValueError("Unknown splitting strategy")

    nr_splits += 1  # Increment the split counter here

    if msg:
        print(f"Splitting on literal {literal}")

    # DPLL on the branch where the literal is true
    clauses_true = set(clauses)
    clauses_true.add(frozenset([literal]))
    if msg:
        nr = 1
        for clause in clauses_true:
            print(f"{indentation} ({nr}) {format_clause(clause)}")
            nr += 1
    result_true, nr_splits = dpll(clauses_true, splitting_strategy, depth + 1, msg=msg, nr_splits=nr_splits)

    if result_true:
        return True, nr_splits  # Formula is satisfiable if true branch works

    # DPLL on the branch where the literal is false
    if msg:
        print(f"\n{indentation}Splitting on literal {-literal}")
    clauses_false = set(clauses)
    clauses_false.add(frozenset([-literal]))
    if msg:
        nr = 1
        for clause in clauses_false:
            print(f"{indentation} ({nr}) {format_clause(clause)}")
            nr += 1

    return dpll(clauses_false, splitting_strategy, depth + 1, msg=msg, nr_splits=nr_splits)  # Try the false branch



def apply_dpll(clauses, msg=True):
    start_time = time.time()
    if msg:
        print("Initial clauses:")
        for i, clause in enumerate(clauses, 1):
            print(f"({i}) {format_clause(clause)}")
        print("-" * 60)
    result, nr_splits= dpll(clauses, splitting_strategy="first", msg=False)# Try "random", "first", "most_frequent",
                                                                                        # "MOMS", "MAMS", "JW", or "DLCS"
    if result:
        print("The formula is SATISFIABLE")
        print("Time measurement: ", time.time() - start_time)
    else:
        if msg:
            print("\nBoth main branches generate ∅")
        print ("The formula is UNSATISFIABLE")
        print("Time measurement: ", time.time() - start_time)
    print("Number of splittings:", nr_splits)


"""
print("\n............Resolution............")
resolution(clauses, msg=False)
"""


"""
print("\n...............DP...............")
davis_putnam(clauses, msg=False)
"""

print("\n...............DPLL...............")
apply_dpll(clauses, msg=False)


"""Simple benchmarks to check resolution, dp, dpll"""
'''
1 -2 0
1 3 0
-2 3 0
-1 2 0
2 -3 0
-1 -3 0 
UNSAT
'''


'''
-1 -2 3 0
1 4 0
2 5 0
-3 0
-6 -4 0
-6 -5 0
-6 0
'''

'''
-1 -2 3 0
1 4 0
2 5 0
-3 5 0
-6 -4 0
-6 -5 0
-6 1 2 0
1 6 0
SAT
'''


'''
1 -2 0
1 3 0
-2 3 0
-1 2 0
2 -3 0
-1 -3 0
1 4 0
-4 2 1 0
4 3 0
-1 4 0
2 4 0
-2 4 0
'''

'''
cnf_1: SAT 5 var, 15 cl 3CNF
RES -> 0.03920
DP -> 0.02903
DPLL -> 0.0

cnf_2: SAT 5 var, 15 cl 3CNF
RES-> 0.0450
DP-> 0.03035
DPLL -> 0.0

cnf_3: SAT 8 var, 20 cl 3CNF
RES -> 93.61717486381531
DP -> 92.4510600566864
DPLL -> 0.00099

cnf_4: SAT 8 var, 20 cl 3CNF
RES -> 56.08901906013489
DP -> 55.29702425003052
DPLL -> 0.0

cnf_5:  10 var, 22 cl 3CNF
RES-> TLE
DP-> TLE
DPLL -> 0.0

cnf_6: 10 var, 22 cl 3CNF
RES-> TLE
DP-> TLE
DPLL -> 0.00092

cnf_7: UNSAT 8 var, 25 cl not 3CNF
RES -> 2.652831792831421
DP -> 0.05481886863708496
DPLL -> 0.0

cnf_8: 10 var, 30 cl, not 3 CNF
RES -> 143.94204926490784
DP -> 132.79472732543945
DPLL -> 0.00097

cnf_9: SAT 15 var 40 cl not 3 CNF 
RES -> TLE
DP -> 0.00001
DPLL -> 0.0

'''