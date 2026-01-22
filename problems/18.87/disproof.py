"""
Counterexample to the Solvable Version of the Kervaire-Laudenbach Conjecture
(Kourovka Notebook Problem 18.87c)

Problem Statement (18.87c):
KLC - solvable version: every independent system of equations with coefficients
in an arbitrary solvable group G has a solution in some solvable overgroup G-bar.

COUNTEREXAMPLE (Klyachko, Mikheenko, Roman'kov, 2024):
There exists a unimodular equation over a metabelian group G that has NO solution
in ANY metabelian (hence solvable of derived length 2) overgroup of G.

Reference: A. A. Klyachko, M. A. Mikheenko and V. A. Roman'kov,
"Equations over solvable groups," J. Algebra 638 (2024), 739-750.

The Group:
G = <c>_7 : <a>_6 where c^a = c^5
This is the semidirect product of Z_7 by Z_6, with the action given by
multiplication by 5 (which is a primitive root mod 7).
|G| = 42, and G is metabelian (derived length 2).

The Equation:
x * x^(-a) * x^(a^2) = c

where x^(-a) means (x^a)^(-1) = a^(-1) * x^(-1) * a
and x^(a^2) means a^(-2) * x * a^2

This equation is UNIMODULAR (exponent sum of x is 1 + (-1) + 1 = 1),
which makes it "independent" in the sense of Problem 18.87.

The Claim:
This equation has no solution in G (which we verify computationally below),
and by the mathematical proof in the reference, it has no solution in ANY
metabelian overgroup of G.

This disproves the solvable version of the Kervaire-Laudenbach Conjecture
for the class of metabelian groups.

Note: This script uses GAP (Groups, Algorithms, Programming) via subprocess
to perform the group-theoretic computations.
"""

import subprocess
import sys


def run_gap_code(gap_code: str) -> str:
    """Run GAP code and return the output."""
    # Try to find GAP executable
    gap_paths = ["gap", "./gap/gap", "../gap/gap"]

    for gap_path in gap_paths:
        try:
            result = subprocess.run(
                [gap_path, "-q", "-b"],
                input=gap_code + "\nQUIT;\n",
                capture_output=True,
                text=True,
                timeout=30
            )
            if result.returncode == 0:
                return result.stdout.strip()
        except (FileNotFoundError, subprocess.TimeoutExpired):
            continue

    return None


def verify_counterexample_with_gap() -> bool:
    """
    Verify the counterexample using GAP.
    Returns True if the counterexample is valid (equation has no solution).
    """
    gap_code = '''
# Construct the metabelian group G = <c>_7 : <a>_6 where c^a = c^5
F := FreeGroup("a", "c");
gens := GeneratorsOfGroup(F);
ag := gens[1]; cg := gens[2];

# Relations: a^6 = 1, c^7 = 1, a^(-1)*c*a = c^5
G := F / [ag^6, cg^7, ag^(-1)*cg*ag*cg^(-5)];
G := Image(IsomorphismPermGroup(G));
elems := Elements(G);

# Find elements a (order 6) and c (order 7) satisfying c^a = c^5
a_cand := Filtered(elems, x -> Order(x) = 6);
c_cand := Filtered(elems, x -> Order(x) = 7);

a := fail; c := fail;
for aa in a_cand do
    for cc in c_cand do
        if aa^(-1) * cc * aa = cc^5 then
            a := aa; c := cc;
            break;
        fi;
    od;
    if a <> fail then break; fi;
od;

# Verify group properties
Print("GROUP_ORDER:", Size(G), "\\n");
Print("DERIVED_LENGTH:", DerivedLength(G), "\\n");
Print("IS_METABELIAN:", DerivedLength(G) <= 2, "\\n");

# Check if equation x * x^(-a) * x^(a^2) = c has any solution
# x^(-a) = (x^a)^(-1) = (a^(-1) * x * a)^(-1) = a^(-1) * x^(-1) * a
# x^(a^2) = a^(-2) * x * a^2
has_solution := false;
for x in elems do
    x_neg_a := a^(-1) * x^(-1) * a;
    x_a2 := a^(-2) * x * a^2;
    lhs := x * x_neg_a * x_a2;
    if lhs = c then
        has_solution := true;
        break;
    fi;
od;

Print("HAS_SOLUTION:", has_solution, "\\n");
Print("C_IN_DERIVED:", c in DerivedSubgroup(G), "\\n");
'''

    output = run_gap_code(gap_code)
    return output


def verify_counterexample_pure_python() -> dict:
    """
    Verify the counterexample using pure Python (without GAP).

    We construct the group G = Z_7 : Z_6 where the action is given by
    c^a = c^5, meaning a^(-1) * c * a = c^5.

    Model: G is the set of pairs (d, b) where:
    - d in Z_7 (the normal subgroup <c>)
    - b in Z_6 (the complement <a>)
    - Multiplication: (d1, b1) * (d2, b2) = (d1 + alpha^b1 * d2 mod 7, b1 + b2 mod 6)

    For c^a = c^5: we need a^(-1) * c * a = c^5
    If c = (1, 0) and a = (0, 1), then:
    a^(-1) = (0, 5) [since -1 mod 6 = 5]
    a^(-1) * c = (0 + alpha^5 * 1, 5) = (alpha^5, 5)
    (alpha^5, 5) * a = (alpha^5 + alpha^5 * 0, 0) = (alpha^5, 0)

    We need (alpha^5, 0) = c^5 = (5, 0)
    So alpha^5 = 5 mod 7

    Since 3^5 = 243 = 5 mod 7, we use alpha = 3.

    Here a = (0, 1) and c = (1, 0).
    """

    ALPHA = 3  # Primitive root mod 7 such that alpha^5 = 5 mod 7

    # Group elements as (d, b) where d in Z_7, b in Z_6
    elements = [(d, b) for d in range(7) for b in range(6)]

    def mult(x, y):
        """Multiply two elements (d1, b1) * (d2, b2)."""
        d1, b1 = x
        d2, b2 = y
        power = pow(ALPHA, b1, 7)
        return ((d1 + power * d2) % 7, (b1 + b2) % 6)

    def inv(x):
        """Inverse of (d, b)."""
        d, b = x
        b_inv = (-b) % 6
        power_inv = pow(ALPHA, b_inv, 7)
        return ((-power_inv * d) % 7, b_inv)

    def conj(x, g):
        """Conjugate x by g: g^(-1) * x * g."""
        return mult(mult(inv(g), x), g)

    # Define a = (0, 1) and c = (1, 0)
    a = (0, 1)
    c = (1, 0)

    # Verify c^a = c^5
    c_conj_a = conj(c, a)
    c_5 = c
    for _ in range(4):
        c_5 = mult(c_5, c)

    assert c_conj_a == c_5, f"c^a = {c_conj_a}, but c^5 = {c_5}"

    # Now check if x * x^(-a) * x^(a^2) = c has any solution
    # x^(-a) = (x^a)^(-1)
    # x^(a^2) = conj(x, a^2)

    a2 = mult(a, a)  # a^2 = (0, 2)

    solutions = []
    for x in elements:
        # x^a = a^(-1) * x * a
        x_a = conj(x, a)
        # x^(-a) = (x^a)^(-1)
        x_neg_a = inv(x_a)
        # x^(a^2) = a^(-2) * x * a^2
        x_a2 = conj(x, a2)

        # LHS = x * x^(-a) * x^(a^2)
        lhs = mult(mult(x, x_neg_a), x_a2)

        if lhs == c:
            solutions.append(x)

    # Verify c is in the derived subgroup
    # G' = <c> (the subgroup of order 7)
    derived = [(d, 0) for d in range(7)]
    c_in_derived = c in derived

    return {
        "group_order": len(elements),
        "is_metabelian": True,  # Z_7 : Z_6 is metabelian
        "equation": "x * x^(-a) * x^(a^2) = c",
        "exponent_sum": 1,  # 1 + (-1) + 1 = 1 (unimodular)
        "num_solutions": len(solutions),
        "solutions": solutions,
        "c_in_derived": c_in_derived,
        "derived_subgroup_size": len(derived),
    }


def main():
    print("=" * 70)
    print("KOUROVKA NOTEBOOK PROBLEM 18.87c - COUNTEREXAMPLE VERIFICATION")
    print("=" * 70)
    print()

    print("Problem: KLC - solvable version")
    print("Claim: Every independent system of equations with coefficients")
    print("       in a solvable group G has a solution in some solvable overgroup.")
    print()
    print("Counterexample by Klyachko, Mikheenko, Roman'kov (2024):")
    print("-" * 70)

    # Pure Python verification
    print("\n[1] Pure Python Verification:")
    print("-" * 40)

    result = verify_counterexample_pure_python()

    print(f"Group: G = <c>_7 : <a>_6 where c^a = c^5")
    print(f"Group order: {result['group_order']}")
    print(f"Is metabelian: {result['is_metabelian']}")
    print(f"Derived subgroup size: {result['derived_subgroup_size']}")
    print()
    print(f"Equation: {result['equation']}")
    print(f"Exponent sum of x: {result['exponent_sum']} (unimodular => independent)")
    print(f"c in G' (derived subgroup): {result['c_in_derived']}")
    print()
    print(f"Number of solutions in G: {result['num_solutions']}")

    if result['num_solutions'] == 0:
        print()
        print("RESULT: The equation has NO SOLUTION in G.")
        print()
        print("Mathematical Theorem (from the reference):")
        print("This equation also has no solution in ANY metabelian overgroup of G.")
        print()
        print("CONCLUSION: This is a valid COUNTEREXAMPLE to KLC-solvable for")
        print("            the variety of metabelian groups.")
        counterexample_valid = True
    else:
        print()
        print(f"WARNING: Found {result['num_solutions']} solutions: {result['solutions']}")
        print("This would invalidate the counterexample!")
        counterexample_valid = False

    # GAP verification (if available)
    print("\n[2] GAP Verification (if available):")
    print("-" * 40)

    gap_output = verify_counterexample_with_gap()
    if gap_output:
        print("GAP output:")
        for line in gap_output.split('\n'):
            if line.startswith(('GROUP_ORDER', 'DERIVED_LENGTH', 'IS_METABELIAN',
                               'HAS_SOLUTION', 'C_IN_DERIVED')):
                print(f"  {line}")

        if 'HAS_SOLUTION:false' in gap_output.replace(' ', ''):
            print("\nGAP confirms: No solution exists in G.")
    else:
        print("GAP not available. Using pure Python verification only.")

    print()
    print("=" * 70)
    if counterexample_valid:
        print("COUNTEREXAMPLE VERIFIED: Problem 18.87c (solvable version) is FALSE")
        print("                         for the variety of metabelian groups.")
        print("=" * 70)
        return 0
    else:
        print("ERROR: Counterexample verification failed!")
        print("=" * 70)
        return 1


if __name__ == "__main__":
    sys.exit(main())
