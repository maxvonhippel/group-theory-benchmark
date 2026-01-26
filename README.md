# 🔮 BuddenBench: A Benchmark of Open Nontrivial Mathematics Research Problems

This benchmark, affectionately named [`budden-bench`](https://x.com/maxvonhippel/status/2014475901384241286?s=20), measures the ability of models and agents to autonomously solve open and important problems in mathematics research. In contrast to other problem sets such as the [Erdős Problems](https://www.erdosproblems.com/), this benchmark is intended to exclusively contain problems which are of ongoing research interest to working mathematicians.

## Inspiration

This project was inspired by the paper [Disproof of the Mertens Conjecture](https://www.sciencedirect.com/science/article/pii/0022314X85900764) which showed how computational algebra systems like GAP can be used to solve longstanding mathematical conjectures by finding counterexamples.

## Tools

- **[GAP (Groups, Algorithms, Programming)](https://www.gap-system.org/)**: A system for computational discrete algebra, especially computational group theory
- **[Lean 4](https://lean-lang.org/)**: An interactive theorem prover for formalizing and verifying mathematical proofs


## AI-Generated Solutions

**Warning**: [No AI-generated proof should be trusted without human review, no matter how formal.](https://www.lesswrong.com/posts/rhAPh3YzhPoBNpgHg/lies-damned-lies-and-proofs-formal-methods-are-not-slopless)

| Problem | List | Artifact | Status | Human Review |
|---------|------|----------|--------|-------------|
| 1.3 | kourovka | [`formalization.lean`](problems/kourovka/problem_1.3/formalization.lean) | Formalized (unsolved) | Pending |
| 1.31 | kourovka | [`formalization.lean`](problems/kourovka/problem_1.31/formalization.lean) | Formalized (unsolved) | Pending |
| 1.35 | kourovka | [`formalization.lean`](problems/kourovka/problem_1.35/formalization.lean) | Formalized (unsolved) | Pending |
| 1.5 | kourovka | [`formalization.lean`](problems/kourovka/problem_1.5/formalization.lean) | Formalized (unsolved) | Pending |
| 1.6 | kourovka | [`formalization.lean`](problems/kourovka/problem_1.6/formalization.lean) | Formalized (unsolved) | Pending |
| 11.44 | kourovka | [`problem.lean`](problems/kourovka/problem_11.44/problem.lean) | Formalized (unsolved) | Pending |
| 16.44 | kourovka | [`cannot_formalize.txt`](problems/kourovka/problem_16.44/cannot_formalize.txt) | Cannot formalize | Pending |
| 19.110 | kourovka | [`cannot_formalize.txt`](problems/kourovka/problem_19.110/cannot_formalize.txt) | Cannot formalize | Pending |
| 5.54 | kourovka | [`cannot_formalize.txt`](problems/kourovka/problem_5.54/cannot_formalize.txt) | Cannot formalize | Pending |
| 9.9 | kourovka | [`cannot_formalize.txt`](problems/kourovka/problem_9.9/cannot_formalize.txt) | Cannot formalize | Pending |
| Well-known problem | kourovka | [`cannot_formalize.txt`](problems/kourovka/problem_Well-known%20problem/cannot_formalize.txt) | Cannot formalize | Pending |

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

*Last updated: 2026-01-26 18:12:14 UTC*
