def resolve(ci, cj):
    for literal in ci:
        if -literal in cj:
            new_clause = (ci- {literal}) | (cj - {-literal})
            if is_tautology(new_clause):
                continue  # Skip tautologies
            return {new_clause}
    return{}

def is_tautology(clause):
    for literal in clause:
        if -literal in clause:
            return True
    return False

def format_clause(clause):
    return "{" + ", ".join(str(x) for x in sorted(clause)) + "}"


def find_unit_literals(clauses):
    return [clause for clause in clauses if len(clause) == 1]



def apply_unit_propagation(clauses, depth=0, msg=True):
    indentation = "  " * depth
    unit_literals = find_unit_literals(clauses)
    while unit_literals:
        unit_clause = unit_literals.pop()
        lit = next(iter(unit_clause))
        new_clauses = []
        if msg:
            print(f"{indentation}Apply one literal rule for {{{lit}}}; delete all clauses containing {lit}")
            print(f"{indentation}Delete {-lit} from the clauses containing it")
        for clause in clauses:
            if lit in clause:
                continue  # Clause is satisfied
            if -lit in clause:
                new_clause = clause - {-lit}
                if len(new_clause) == 0:
                    if msg:
                        print(f"{indentation}Removing literal {-lit} from clause {format_clause(clause)} it generates ∅")
                    return False
                if len(new_clause) == 1:
                    unit_literals.append(new_clause)
                new_clauses.append(new_clause)
            else:
                new_clauses.append(clause)
        clauses = set(new_clauses)
        if msg:
            nr = 1
            print(f"{indentation}Remaining clauses:")
            for c in clauses:
                print(f"{indentation} ({nr}) {format_clause(c)}")
                nr += 1
    return clauses


def apply_pure_literal_rule(clauses, depth=0, msg=True):
    """Apply the pure literal rule to the clauses."""
    indentation="    " * depth
    while True:
        pure_literals = {lit for clause in clauses for lit in clause if -lit not in {l for c in clauses for l in c}}  # Find pure literals

        if not pure_literals:
            break  # Exit loop if no pure literals are found

        if msg:
            print(f"{indentation}Apply pure literal rule - pure literals are {', '.join(map(str, pure_literals))}")
        # Remove clauses that are satisfied by pure literals
        clauses = {clause for clause in clauses if not clause & pure_literals}

        # Print remaining clauses after applying the rule
        if clauses and msg:
            nr=1
            print(f"{indentation}Remaining clauses:")
            for clause in clauses:
                print(f"{indentation} ({nr}) {format_clause(clause)}")
                nr+=1

        if not clauses:  # If no clauses are left, the formula is trivially satisfied
            if msg:
                print(f"{indentation}No remaining clauses")
            return {}

    return clauses
