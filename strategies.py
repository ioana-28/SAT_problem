import random
from collections import Counter
from functions import *

# Splitting Strategy Functions
def choose_literal_random(clauses):
    """Choose a random literal from the clauses."""
    all_literals = {lit for clause in clauses for lit in clause}
    return random.choice(list(all_literals))


def choose_literal_first(clauses):
    """Choose the first literal from the first clause."""
    clauses_list=list(clauses)
    return next(iter(clauses_list[0]))


def choose_literal_most_frequent(clauses):
    """Choose the most frequent literal from the clauses."""
    literal_count = Counter(lit for clause in clauses for lit in clause)
    return max(literal_count, key=literal_count.get)




def choose_literal_MOMS(clauses):
    """Choose a literal based on the MOMS heuristic (Maximum Occurrences in Minimum Size clauses)."""
    # Step 1: Find clauses with minimum size
    min_size = min(len(clause) for clause in clauses)
    min_clauses = [clause for clause in clauses if len(clause) == min_size]

    # Step 2: Count literals only in minimum size clauses
    literal_count = Counter(lit for clause in min_clauses for lit in clause)

    # Step 3: Pick the literal that occurs most often among them
    return max(literal_count, key=literal_count.get)

def choose_literal_MAMS(clauses):
    """Choose a literal based on the MAMS heuristic (Maximum Among Minimum Size and All)."""
    # Step 1: Count literals in all clauses
    counter_all = Counter(lit for clause in clauses for lit in clause)

    # Step 2: Focus on clauses of minimum size
    min_size = min(len(clause) for clause in clauses)
    min_clauses = [clause for clause in clauses if len(clause) == min_size]
    counter_min = Counter(lit for clause in min_clauses for lit in clause)

    # Step 3: Pick the literal that maximizes (global count + count of negation in min-clauses)
    best_literal = None
    best_score = -1
    all_literals = set(counter_all.keys())
    for lit in all_literals:
        score = counter_all[lit] + counter_min[-lit]
        if score > best_score:
            best_score = score
            best_literal = lit

    return best_literal

def choose_literal_JW(clauses):
    """Choose a literal based on the Jeroslow-Wang (JW) heuristic using exponential weighting."""
    # Step 1: Compute JW scores
    jw_scores = Counter()

    for clause in clauses:
        weight = 2 ** (-len(clause))  # Exponential weight
        for lit in clause:
            jw_scores[lit] += weight

    # Step 2: Choose the literal with the highest JW score
    best_literal = None
    best_score = -1.0
    for lit in jw_scores:
        if jw_scores[lit] > best_score:
            best_score = jw_scores[lit]
            best_literal = lit

    return best_literal



def choose_literal_DLCS(clauses):
    """
    Choose the literal based on DLCS (Dynamic Largest Combined Sum).
    Count both positive and negative occurrences of each variable,
    then choose the variable with the highest combined count.
    """
    pos_count = Counter()
    neg_count = Counter()

    for clause in clauses:
        for lit in clause:
            if lit > 0:
                pos_count[lit] += 1
            else:
                neg_count[-lit] += 1  # store as positive var

    all_vars = set(pos_count.keys()) | set(neg_count.keys())

    best_var = None
    best_score = -1
    best_polarity = True

    for var in all_vars:
        score = pos_count[var] + neg_count[var]
        if score > best_score:
            best_score = score
            best_var = var
            best_polarity = pos_count[var] >= neg_count[var]  # prefer more common polarity

    return best_var if best_polarity else -best_var


