# Ariadne SMT

[![macOS Status](https://github.com/ariadne-cps/smt/actions/workflows/macos.yml/badge.svg)](https://github.com/ariadne-cps/smt/actions/workflows/macos.yml)
[![Ubuntu Status](https://github.com/ariadne-cps/smt/actions/workflows/ubuntu.yml/badge.svg)](https://github.com/ariadne-cps/smt/actions/workflows/ubuntu.yml)
[![Windows Status](https://github.com/ariadne-cps/smt/actions/workflows/win.yml/badge.svg)](https://github.com/ariadne-cps/smt/actions/workflows/win.yml)
[![Sanitizers Status](https://github.com/ariadne-cps/smt/actions/workflows/sanitizers.yml/badge.svg)](https://github.com/ariadne-cps/smt/actions/workflows/sanitizers.yml)
[![Coverage Status](https://github.com/ariadne-cps/smt/actions/workflows/coverage.yml/badge.svg)](https://github.com/ariadne-cps/smt/actions/workflows/coverage.yml)
[![codecov](https://codecov.io/gh/ariadne-cps/smt/branch/main/graph/badge.svg)](https://codecov.io/gh/ariadne-cps/smt)

Ariadne SMT is the standalone C++20 **epsilon-SMT solver for bounded real constraints** in Ariadne. It combines Boolean reasoning with validated real-constraint evaluation, interval-based pruning and subdivision to search for epsilon-satisfying witnesses or establish unsatisfiability when possible. Results distinguish **UNSAT**, **EPSILON_SAT** and **UNKNOWN**; an unknown result must not be interpreted as satisfiability or unsatisfiability.
Although independently maintained and usable, this repository is also part of the [Ariadne repository structure](https://github.com/ariadne-cps/ariadne/blob/main/doc/structure.md).

This repository is dedicated to the epsilon-SMT solver. General-purpose symbolic expressions belong to [Ariadne Symbolic](https://github.com/ariadne-cps/symbolic); validated constraint solving and equation solving belong to their respective modular Ariadne repositories. The benchmarks here evaluate the epsilon-SMT solver and its internal theory-reasoning strategies rather than exposing separate general-purpose solver products.

## Layout

The public API lives in `include/smt`, with umbrella header `include/ariadne-smt.hpp`. The solver implementation is under `src`, the C++ regression suite under `tests`, performance and solver-strategy benchmarks under `benchmarks`, the design journal under `doc/designs`, Python bindings and tests under `python`, and standalone examples under `tutorials/tutorial_smt`.

## Dependencies

SMT depends directly on:

- [ariadne-cps/build](https://github.com/ariadne-cps/build) (`ss/bui`; shared CMake configuration).
- [ariadne-cps/benchmarking](https://github.com/ariadne-cps/benchmarking) (`ss/bmk`; standalone benchmark support only).
- [ariadne-cps/cdcl](https://github.com/ariadne-cps/cdcl) (`ss/cdc`; Boolean search engine).
- [ariadne-cps/symbolic](https://github.com/ariadne-cps/symbolic) (`ss/sym`; symbolic expressions).
- [ariadne-cps/constraint-solving](https://github.com/ariadne-cps/constraint-solving) (`ss/csl`; validated pruning).
- [ariadne-cps/equation-solving](https://github.com/ariadne-cps/equation-solving) (`ss/equ`; interval Newton methods).
- [ariadne-cps/threading](https://github.com/ariadne-cps/threading) (`ss/thr`; workload scheduling and thread-management facilities).

The lower Function, Geometry, Algebra, Utility and Python Common dependencies are supplied transitively. CMake checks that common dependencies, including Configuration, Logging and Utility, are pinned to consistent commits. SMT no longer uses the old monolithic Kernel.

The Release CI builds the `benchmarks` target only after the library and
Python bindings. It does **not** execute benchmarks. The standalone benchmark
executables use the shared Benchmarking CLI, timing and reporting facilities.
The Interval Newton benchmark retains its diagnostic modes and uses the
Runner for repeated solver timings. The Barr3 benchmark reports repeated
solver-query measurements using Runner and Report. Invoke these executables
manually when benchmarking is desired.

The Barr3 benchmark uses `SmtSolver` directly to verify the unsafe-region and Lie-derivative constraints derived from the published Barr3 2-64-64-1 neural barrier. The previous X-Taylor and other exploratory numerical profiles have been removed. No Linear Programming dependency is required.

## Build

```bash
git clone --recurse-submodules https://github.com/ariadne-cps/smt.git
cd smt
cmake -S . -B build -DCMAKE_BUILD_TYPE=Release
cmake --build build --parallel --target ariadne-smt pyariadne
cmake --build build --parallel --target benchmarks
ctest --test-dir build --output-on-failure
```

The standalone C++ tutorial is in `tutorials/tutorial_smt`, and the Python tutorial is `python/tutorials/tutorial_smt.py`. Both illustrate epsilon-SMT solving, including satisfiable and unsatisfiable bounded-real formulas and Boolean combinations.

## Python bindings

With a compatible Python development environment, the standalone build produces and installs the combined `pyariadne` extension, containing the Symbolic, CDCL, Constraint Solving, Equation Solving and SMT bindings and their transitive dependencies. The SMT classes are exposed as `SmtSolver`, `SmtSolverConfiguration` and `SmtResult`; `pyariadne-smt` is an internal CMake target, not a separate Python module.

## Contribution guidelines

If you would like to contribute to Ariadne SMT, please contact the developer:

- Luca Geretti <luca.geretti@univr.it>
