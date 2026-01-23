# 🔮 BuddenBench: a Benchmark of Open Nontrivial Group Theory Problems

This benchmark, affectionately named [`budden-bench`](https://x.com/maxvonhippel/status/2014475901384241286?s=20), measures the ability of models and agents to autonomously solve open and important problems in mathematics, specifically group theory. In contrast to other problem sets such as the [Erdős Problems](https://www.erdosproblems.com/), this benchmark contains exclusively problems which are not just unsolved but also the objects of ongoing mathematical attention, i.e., which are nontrivial.

## Inspiration

This project was inspired by the paper [Disproof of the Mertens Conjecture](https://www.sciencedirect.com/science/article/pii/0022314X85900764) which showed how computational algebra systems like GAP can be used to solve longstanding mathematical conjectures by finding counterexamples.

## Tools

- **[GAP (Groups, Algorithms, Programming)](https://www.gap-system.org/)**: A system for computational discrete algebra, especially computational group theory
- **[Lean 4](https://lean-lang.org/)**: An interactive theorem prover for formalizing and verifying mathematical proofs


## AI-Generated Solutions

**Warning**: [No AI-generated proof should be trusted without human review, no matter how formal.](https://www.lesswrong.com/posts/rhAPh3YzhPoBNpgHg/lies-damned-lies-and-proofs-formal-methods-are-not-slopless)

| Problem | Artifact | Status | Human Review |
|---------|----------|--------|-------------|
| problem_219 | `formalization_attempt_summary.txt` | Could not formalize | Pending |
| problem_700 | `formalization_attempt_summary.txt` | Could not formalize | Pending |

## Setup

```bash
make setup  # Install dependencies, build GAP, setup Lean
```

## Usage

```bash
make watch-solve  # Launch Claude to solve a random problem
make test         # Run test suite
```

## Problem Set

Problems are drawn from the [Kourovka Notebook](https://kourovka-notebook.org/), a collection of unsolved problems in group theory.
