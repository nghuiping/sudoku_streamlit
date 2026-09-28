"""IT5005 Assignment 1: student implementation file.

Implement the functions marked below. Do not modify utils.py or logic_.py.
"""

from utils import *
from logic_ import *


# Do not change this function; it is used to create atomic propositions.
def atom(prefix, r, c, v):
    """prefix is 'Is' or 'Not'. Returns the Expr for e.g. Is3_2_4."""
    return expr(f'{prefix}{r}_{c}_{v}')


def build_general_kb(n, box_h, box_w, givens):
    kb = PropKB()
    for r in range(1, n+1):
        for c in range(1, n+1):
            options = []
            for v in range(1, n+1): #can take 9 values
                options.append(atom('Is', r, c, v))
            kb.tell(Expr('|', *options))

    for r in range(1, n+1):
        for c in range(1, n+1):
            for v1 in range(1, n+1):
                for v2 in range(v1+1, n+1): #in the same cell, it can only be one value
                    kb.tell(~atom('Is', r, c, v1) | ~atom('Is', r, c, v2))

    for r in range(1, n+1):
        for v in range(1, n+1):
            for c1 in range(1, n+1):
                for c2 in range(c1+1, n+1): #in the same row, one value cannot occupy same two columns
                    kb.tell(~atom('Is', r, c1, v) | ~atom('Is', r, c2, v))

    for c in range(1, n+1):
        for v in range(1, n+1):
            for r1 in range(1, n+1):
                for r2 in range(r1+1, n+1): #in the same column, one value cannot occupy same two rows
                    kb.tell(~atom('Is', r1, c, v) | ~atom('Is', r2, c, v))

    for boxr in range(1, n+1, box_h):
        for boxc in range(1, n+1, box_w):
            cells = []
            for r in range(boxr, boxr + box_h):
                for c in range(boxc, boxc + box_w):
                    cells.append((r,c))
            for v in range(1, n+1): #fix the value and compare the cells
                for i in range(len(cells)):
                    for j in range(i+1, len(cells)):
                        r1, c1 = cells[i]
                        r2, c2 = cells[j]
                        kb.tell(~atom('Is', r1, c1, v) | ~atom('Is', r2, c2, v))

    for (r, c), v in givens.items():
        kb.tell(atom('Is', r, c, v))

    return kb


def build_definite_kb(n, box_h, box_w, givens):
    kb = PropDefiniteKB()

    for (r, c), v in givens.items():
        kb.tell(atom('Is', r, c, v))

    for r in range(1, n+1): #eliminate other values from that cell
        for c in range(1, n+1):
            for v1 in range(1, n+1):
                for v2 in range(1, n+1):
                    if v1 != v2:
                        kb.tell(atom('Is', r, c, v1) | '==>' | atom('Not', r, c, v2)) #cannot do v1+1 because you need to check backwards

    for r in range(1, n+1): #eliminate other values from the row
        for v in range(1, n+1):
            for c1 in range(1, n+1):
                for c2 in range(1, n+1):
                    if c1 != c2:
                        kb.tell(atom('Is', r, c1, v) | '==>' | atom('Not', r, c2, v))

    for c in range(1, n+1): #eliminate other values from the column
        for v in range(1, n+1):
            for r1 in range(1, n+1):
                for r2 in range(1, n+1):
                    if r1 != r2:
                        kb.tell(atom('Is', r1, c, v) | '==>' | atom('Not', r2, c, v))

    for boxr in range(1, n+1, box_h):
        for boxc in range(1, n+1, box_w):
            cells = []
            for r in range(boxr, boxr + box_h):
                for c in range(boxc, boxc + box_w):
                    cells.append((r,c))
            for v in range(1, n+1): #fix the value and compare the cells
                for r1, c1 in cells:
                    for r2, c2 in cells:
                        if (r1, c1) != (r2, c2):
                            kb.tell(atom('Is', r1, c1, v) | '==>' | atom('Not', r2, c2, v))

    for r in range(1, n+1):
        for c in range(1, n+1):
            for v in range(1, n+1):
                premises = [] #for every v, maintain one premise
                for otherv in range(1, n+1):
                    if otherv != v:
                        premises.append(atom('Not', r, c, otherv))
                kb.tell(Expr('&',*premises) | '==>' | atom('Is', r, c, v))
     
    return kb

def solve_full_grid_fc(n, box_h, box_w, givens):
    kb = build_definite_kb(n, box_h, box_w, givens)
    inferred = pl_fc_infer_all(kb)
    solution = dict(givens)

    for r in range(1, n+1):
        for c in range(1, n+1):
            if (r,c) in givens:
                continue
            for v in range(1, n+1):
                if atom('Is', r, c, v) in inferred:
                    solution[(r, c)] = v
                    break
    return solution 

def pl_bc_entails(kb, query):

    # Build the backward-chaining index once
    if not hasattr(kb, '_bc_rules'):
        kb._bc_rules = defaultdict(list)
        kb._bc_facts = set()

        for clause in kb.clauses:

            if clause.op == '==>':
                premises, conclusion = parse_definite_clause(clause)
                kb._bc_rules[conclusion].append(premises)

            else:
                kb._bc_facts.add(clause)

        # Cache facts/propositions successfully proved
        kb._bc_proven = set(kb._bc_facts)

        # Version increases whenever BC discovers something new
        kb._bc_version = 0

        # failed[goal] = version at which it failed
        kb._bc_failed = {}

    def prove(goal, visiting):

        # Already known/proved
        if goal in kb._bc_proven:
            return True

        # Prevent cycles
        if goal in visiting:
            return False

        # Already failed when our known information was unchanged
        if kb._bc_failed.get(goal) == kb._bc_version:
            return False

        start_version = kb._bc_version

        visiting.add(goal)

        # Only examine rules whose conclusion is this goal
        for premises in kb._bc_rules.get(goal, []):

            if all(prove(p, visiting) for p in premises):

                visiting.remove(goal)

                if goal not in kb._bc_proven:
                    kb._bc_proven.add(goal)
                    kb._bc_version += 1

                return True

        visiting.remove(goal)

        # Only remember failure if nothing new was learned
        # while exploring this goal
        if kb._bc_version == start_version:
            kb._bc_failed[goal] = kb._bc_version

        return False

    # A failed attempt may still have discovered useful intermediate facts.
    # Retry while BC is still learning new facts.
    while True:

        version = kb._bc_version

        if prove(query, set()):
            return True

        # Nothing new was discovered, so this really is unprovable
        if kb._bc_version == version:
            return False

def solve_full_grid_bc(n, box_h, box_w, givens):

    kb = build_definite_kb(n, box_h, box_w, givens)
    solution = dict(givens)

    for r in range(1, n + 1):
        for c in range(1, n + 1):

            # Already given
            if (r, c) in givens:
                continue

            # Try every possible value
            for v in range(1, n + 1):

                if pl_bc_entails(
                    kb,
                    atom('Is', r, c, v)
                ):
                    solution[(r, c)] = v
                    break

    return solution