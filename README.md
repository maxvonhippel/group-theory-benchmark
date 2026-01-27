# 🔮 BuddenBench: A Benchmark of Open Nontrivial Mathematics Research Problems

This benchmark, affectionately named [`budden-bench`](https://x.com/maxvonhippel/status/2014475901384241286?s=20), measures the ability of models and agents to autonomously solve open and important problems in mathematics research. In contrast to other problem sets such as the [Erdős Problems](https://www.erdosproblems.com/), this benchmark is intended to exclusively contain problems which are of ongoing research interest to working mathematicians.

## Inspiration

This project was inspired by the paper [Disproof of the Mertens Conjecture](https://www.sciencedirect.com/science/article/pii/0022314X85900764) which showed how computational algebra systems like GAP can be used to solve longstanding mathematical conjectures by finding counterexamples.

## Tools

- **[GAP (Groups, Algorithms, Programming)](https://www.gap-system.org/)**: A system for computational discrete algebra, especially computational group theory
- **[Lean 4](https://lean-lang.org/)**: An interactive theorem prover for formalizing and verifying mathematical proofs


## AI-Generated Solutions

**Warning**: [No AI-generated proof should be trusted without human review, no matter how formal.](https://www.lesswrong.com/posts/rhAPh3YzhPoBNpgHg/lies-damned-lies-and-proofs-formal-methods-are-not-slopless)

**Legend**: <span style="color: green">✓ Success</span> | <span style="color: red">✗ Cannot formalize</span> | <span style="color: orange">⚠ Unverified</span> | <span style="color: purple">★ New result</span> | <span style="color: gray">? Unknown</span>

| Problem | List | Artifact | Status | Human Review |
|---------|------|----------|--------|-------------|
| 1 | green | [`formalization.lean`](problems/green/problem_1/formalization.lean) | <span style="color: green">✓ Formalized (unsolved)</span> | Pending |
| 10 | green | [`cannot_formalize.txt`](problems/green/problem_10/cannot_formalize.txt) | <span style="color: red">✗ Cannot formalize</span> | Pending |
| 11 | green | [`cannot_formalize.txt`](problems/green/problem_11/cannot_formalize.txt) | <span style="color: red">✗ Cannot formalize</span> | Pending |
| 12 | green | [`formalization.lean`](problems/green/problem_12/formalization.lean) | <span style="color: green">✓ Formalized (unsolved)</span> | Pending |
| 13 | green | [`cannot_formalize.txt`](problems/green/problem_13/cannot_formalize.txt) | <span style="color: red">✗ Cannot formalize</span> | Pending |
| 15 | green | [`formalization.lean`](problems/green/problem_15/formalization.lean) | <span style="color: green">✓ Formalized (unsolved)</span> | Pending |
| 2 | green | [`formalization.lean`](problems/green/problem_2/formalization.lean) | <span style="color: green">✓ Formalized (unsolved)</span> | Pending |
| 3 | green | [`formalization.lean`](problems/green/problem_3/formalization.lean) | <span style="color: green">✓ Formalized (unsolved)</span> | Pending |
| 5 | green | [`cannot_formalize.txt`](problems/green/problem_5/cannot_formalize.txt) | <span style="color: red">✗ Cannot formalize</span> | Pending |
| 6 | green | [`formalization.lean`](problems/green/problem_6/formalization.lean) | <span style="color: green">✓ Formalized (unsolved)</span> | Pending |
| 8 | green | [`cannot_formalize.txt`](problems/green/problem_8/cannot_formalize.txt) | <span style="color: red">✗ Cannot formalize</span> | Pending |
| 9 | green | [`cannot_formalize.txt`](problems/green/problem_9/cannot_formalize.txt) | <span style="color: red">✗ Cannot formalize</span> | Pending |
| K-2 | klee | [`formalization.lean`](problems/klee/problem_K-2/formalization.lean) | <span style="color: green">✓ Formalized (unsolved)</span> | Pending |
| K-4 | klee | [`formalization.lean`](problems/klee/problem_K-4/formalization.lean) | <span style="color: green">✓ Formalized (unsolved)</span> | Pending |
| K-8 | klee | [`formalization.lean`](problems/klee/problem_K-8/formalization.lean) | <span style="color: green">✓ Formalized (unsolved)</span> | Pending |
| K1 | klee | [`formalization.lean`](problems/klee/problem_K1/formalization.lean) | <span style="color: green">✓ Formalized (unsolved)</span> | Pending |
| K12 | klee | [`cannot_formalize.txt`](problems/klee/problem_K12/cannot_formalize.txt) | <span style="color: red">✗ Cannot formalize</span> | Pending |
| K3 | klee | [`formalization.lean`](problems/klee/problem_K3/formalization.lean) | <span style="color: green">✓ Formalized (unsolved)</span> | Pending |
| K4 | klee | [`formalization.lean`](problems/klee/problem_K4/formalization.lean) | <span style="color: green">✓ Formalized (unsolved)</span> | Pending |
| K6 | klee | [`formalization.lean`](problems/klee/problem_K6/formalization.lean) | <span style="color: green">✓ Formalized (unsolved)</span> | Pending |
| 1.12 | kourovka | [`cannot_formalize.txt`](problems/kourovka/problem_1.12/cannot_formalize.txt) | <span style="color: red">✗ Cannot formalize</span> | Pending |
| 1.20 | kourovka | [`cannot_formalize.txt`](problems/kourovka/problem_1.20/cannot_formalize.txt) | <span style="color: red">✗ Cannot formalize</span> | Pending |
| 1.27 | kourovka | [`cannot_formalize.txt`](problems/kourovka/problem_1.27/cannot_formalize.txt) | <span style="color: red">✗ Cannot formalize</span> | Pending |
| 1.28 | kourovka | [`cannot_formalize.txt`](problems/kourovka/problem_1.28/cannot_formalize.txt) | <span style="color: red">✗ Cannot formalize</span> | Pending |
| 1.3 | kourovka | [`formalization.lean`](problems/kourovka/problem_1.3/formalization.lean) | <span style="color: green">✓ Formalized (unsolved)</span> | Pending |
| 1.31 | kourovka | [`formalization.lean`](problems/kourovka/problem_1.31/formalization.lean) | <span style="color: green">✓ Formalized (unsolved)</span> | Pending |
| 1.33 | kourovka | [`cannot_formalize.txt`](problems/kourovka/problem_1.33/cannot_formalize.txt) | <span style="color: red">✗ Cannot formalize</span> | Pending |
| 1.35 | kourovka | [`formalization.lean`](problems/kourovka/problem_1.35/formalization.lean) | <span style="color: green">✓ Formalized (unsolved)</span> | Pending |
| 1.40 | kourovka | [`formalization.lean`](problems/kourovka/problem_1.40/formalization.lean) | <span style="color: green">✓ Formalized (unsolved)</span> | Pending |
| 1.46 | kourovka | [`cannot_formalize.txt`](problems/kourovka/problem_1.46/cannot_formalize.txt) | <span style="color: red">✗ Cannot formalize</span> | Pending |
| 1.5 | kourovka | [`formalization.lean`](problems/kourovka/problem_1.5/formalization.lean) | <span style="color: green">✓ Formalized (unsolved)</span> | Pending |
| 1.51 | kourovka | [`cannot_formalize.txt`](problems/kourovka/problem_1.51/cannot_formalize.txt) | <span style="color: red">✗ Cannot formalize</span> | Pending |
| 1.54 | kourovka | [`cannot_formalize.txt`](problems/kourovka/problem_1.54/cannot_formalize.txt) | <span style="color: red">✗ Cannot formalize</span> | Pending |
| 1.55 | kourovka | [`cannot_formalize.txt`](problems/kourovka/problem_1.55/cannot_formalize.txt) | <span style="color: red">✗ Cannot formalize</span> | Pending |
| 1.6 | kourovka | [`formalization.lean`](problems/kourovka/problem_1.6/formalization.lean) | <span style="color: green">✓ Formalized (unsolved)</span> | Pending |
| 1.67 | kourovka | [`cannot_formalize.txt`](problems/kourovka/problem_1.67/cannot_formalize.txt) | <span style="color: red">✗ Cannot formalize</span> | Pending |
| 1.74 | kourovka | [`cannot_formalize.txt`](problems/kourovka/problem_1.74/cannot_formalize.txt) | <span style="color: red">✗ Cannot formalize</span> | Pending |
| 1.86 | kourovka | [`cannot_formalize.txt`](problems/kourovka/problem_1.86/cannot_formalize.txt) | <span style="color: red">✗ Cannot formalize</span> | Pending |
| 1.87 | kourovka | [`cannot_formalize.txt`](problems/kourovka/problem_1.87/cannot_formalize.txt) | <span style="color: red">✗ Cannot formalize</span> | Pending |
| 11.44 | kourovka | [`problem.lean`](problems/kourovka/problem_11.44/problem.lean) | <span style="color: green">✓ Formalized (unsolved)</span> | Pending |
| 16.44 | kourovka | [`cannot_formalize.txt`](problems/kourovka/problem_16.44/cannot_formalize.txt) | <span style="color: red">✗ Cannot formalize</span> | Pending |
| 19.110 | kourovka | [`cannot_formalize.txt`](problems/kourovka/problem_19.110/cannot_formalize.txt) | <span style="color: red">✗ Cannot formalize</span> | Pending |
| 2.22 | kourovka | [`cannot_formalize.txt`](problems/kourovka/problem_2.22/cannot_formalize.txt) | <span style="color: red">✗ Cannot formalize</span> | Pending |
| 2.6 | kourovka | [`cannot_formalize.txt`](problems/kourovka/problem_2.6/cannot_formalize.txt) | <span style="color: red">✗ Cannot formalize</span> | Pending |
| 2.9 | kourovka | [`cannot_formalize.txt`](problems/kourovka/problem_2.9/cannot_formalize.txt) | <span style="color: red">✗ Cannot formalize</span> | Pending |
| 5.54 | kourovka | [`cannot_formalize.txt`](problems/kourovka/problem_5.54/cannot_formalize.txt) | <span style="color: red">✗ Cannot formalize</span> | Pending |
| 9.9 | kourovka | [`cannot_formalize.txt`](problems/kourovka/problem_9.9/cannot_formalize.txt) | <span style="color: red">✗ Cannot formalize</span> | Pending |
| Well-known problem | kourovka | [`cannot_formalize.txt`](problems/kourovka/problem_Well-known%20problem/cannot_formalize.txt) | <span style="color: red">✗ Cannot formalize</span> | Pending |
| 3.1 | mazya | [`cannot_formalize.txt`](problems/mazya/problem_3.1/cannot_formalize.txt) | <span style="color: red">✗ Cannot formalize</span> | Pending |
| 3.11 | mazya | [`cannot_formalize.txt`](problems/mazya/problem_3.11/cannot_formalize.txt) | <span style="color: red">✗ Cannot formalize</span> | Pending |
| 3.12 | mazya | [`cannot_formalize.txt`](problems/mazya/problem_3.12/cannot_formalize.txt) | <span style="color: red">✗ Cannot formalize</span> | Pending |
| 3.13 | mazya | [`cannot_formalize.txt`](problems/mazya/problem_3.13/cannot_formalize.txt) | <span style="color: red">✗ Cannot formalize</span> | Pending |
| 3.3 | mazya | [`cannot_formalize.txt`](problems/mazya/problem_3.3/cannot_formalize.txt) | <span style="color: red">✗ Cannot formalize</span> | Pending |
| 3.4 | mazya | [`cannot_formalize.txt`](problems/mazya/problem_3.4/cannot_formalize.txt) | <span style="color: red">✗ Cannot formalize</span> | Pending |
| 3.5 | mazya | [`cannot_formalize.txt`](problems/mazya/problem_3.5/cannot_formalize.txt) | <span style="color: red">✗ Cannot formalize</span> | Pending |
| 3.6 | mazya | [`cannot_formalize.txt`](problems/mazya/problem_3.6/cannot_formalize.txt) | <span style="color: red">✗ Cannot formalize</span> | Pending |
| 3.9 | mazya | [`cannot_formalize.txt`](problems/mazya/problem_3.9/cannot_formalize.txt) | <span style="color: red">✗ Cannot formalize</span> | Pending |
| 4.1 | mazya | [`cannot_formalize.txt`](problems/mazya/problem_4.1/cannot_formalize.txt) | <span style="color: red">✗ Cannot formalize</span> | Pending |
| 4.2 | mazya | [`cannot_formalize.txt`](problems/mazya/problem_4.2/cannot_formalize.txt) | <span style="color: red">✗ Cannot formalize</span> | Pending |
| 4.3 | mazya | [`cannot_formalize.txt`](problems/mazya/problem_4.3/cannot_formalize.txt) | <span style="color: red">✗ Cannot formalize</span> | Pending |
| 4.4 | mazya | [`cannot_formalize.txt`](problems/mazya/problem_4.4/cannot_formalize.txt) | <span style="color: red">✗ Cannot formalize</span> | Pending |
| 4.5 | mazya | [`cannot_formalize.txt`](problems/mazya/problem_4.5/cannot_formalize.txt) | <span style="color: red">✗ Cannot formalize</span> | Pending |
| 1 | ramm | [`cannot_formalize.txt`](problems/ramm/problem_1/cannot_formalize.txt) | <span style="color: red">✗ Cannot formalize</span> | Pending |
| 2 | ramm | [`cannot_formalize.txt`](problems/ramm/problem_2/cannot_formalize.txt) | <span style="color: red">✗ Cannot formalize</span> | Pending |
| 3.1 | ramm | [`cannot_formalize.txt`](problems/ramm/problem_3.1/cannot_formalize.txt) | <span style="color: red">✗ Cannot formalize</span> | Pending |
| 3.2 | ramm | [`cannot_formalize.txt`](problems/ramm/problem_3.2/cannot_formalize.txt) | <span style="color: red">✗ Cannot formalize</span> | Pending |
| 4 | ramm | [`cannot_formalize.txt`](problems/ramm/problem_4/cannot_formalize.txt) | <span style="color: red">✗ Cannot formalize</span> | Pending |

## Setup

```bash
make setup  # Install dependencies, build GAP, setup Lean
```

## Usage

```bash
make watch-solve  # Launch Claude to solve a random problem
make test         # Run test suite
```

## Problem Sets

Problems are drawn from multiple sources:

- **[Kourovka Notebook](https://kourovka-notebook.org/)**: A collection of unsolved problems in group theory
- **[Unsolved Problems in Intuitive Geometry](https://sites.math.washington.edu//~reu/papers/2010/mark/Unsolved_Problems_In_Intuitive_Geometry.pdf)** by Klee & Wagon: Open problems in computational and combinatorial geometry
- **[100 Open Problems](https://arxiv.org/abs/2404.07513)** by Ben Green: Research-level problems in additive combinatorics and number theory
- **Some open problems in analysis** by A.G. Ramm: Open problems in Radon transforms, operator theory, and PDEs
- **Seventy Five (Thousand) Unsolved Problems in Analysis and PDEs** by Vladimir Maz'ya: Comprehensive collection of open problems in analysis and partial differential equations

## Citation

If you use this benchmark in your research, please cite:

```bibtex
@dataset{vonhippel2025budden,
  author={von Hippel, Max},
  title={{BuddenBench}: A Benchmark of Open Nontrivial Mathematics Research Problems},
  year={2025},
  publisher={GitHub},
  howpublished={\url{https://github.com/maxvonhippel/budden-bench}},
  note={AI benchmark for automated mathematics research in group theory and geometry}
}
```

For citations to the source problem collections, see [references.bib](references.bib).

*Last updated: 2026-01-27 03:29:20 UTC*
