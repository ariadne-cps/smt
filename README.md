# Ariadne SMT

[![License: GPL v3](https://img.shields.io/badge/License-GPL%20v3-blue.svg)](https://www.gnu.org/licenses/gpl-3.0)
[![Unix Status](https://github.com/ariadne-cps/smt/actions/workflows/unix.yml/badge.svg)](https://github.com/ariadne-cps/smt/actions/workflows/unix.yml)
[![Windows Status](https://github.com/ariadne-cps/smt/actions/workflows/win.yml/badge.svg)](https://github.com/ariadne-cps/smt/actions/workflows/win.yml)
[![Sanitizers Status](https://github.com/ariadne-cps/smt/actions/workflows/sanitizers.yml/badge.svg)](https://github.com/ariadne-cps/smt/actions/workflows/sanitizers.yml)
[![Coverage Status](https://github.com/ariadne-cps/smt/actions/workflows/coverage.yml/badge.svg)](https://github.com/ariadne-cps/smt/actions/workflows/coverage.yml)
[![codecov](https://codecov.io/gh/ariadne-cps/smt/branch/main/graph/badge.svg)](https://codecov.io/gh/ariadne-cps/smt)

Ariadne SMT is the standalone C++20 **epsilon-SMT solver for bounded real constraints** in Ariadne. It combines Boolean reasoning with validated real-constraint evaluation, interval-based pruning and subdivision to search for epsilon-satisfying witnesses or establish unsatisfiability when possible. Results distinguish **UNSAT**, **EPSILON_SAT** and **UNKNOWN**; an unknown result must not be interpreted as satisfiability or unsatisfiability.

This repository is dedicated to the epsilon-SMT solver. General-purpose symbolic expressions belong to [Ariadne Symbolic](https://github.com/ariadne-cps/symbolic); validated constraint solving and equation solving belong to their respective modular Ariadne repositories. The benchmarks here evaluate the epsilon-SMT solver and its internal theory-reasoning strategies rather than exposing separate general-purpose solver products.

## Layout

The public API lives in `include/smt`, with umbrella header `include/ariadne-smt.hpp`. The solver implementation is under `src`, the C++ regression suite under `tests`, performance and solver-strategy benchmarks under `benchmarks`, the design journal under `doc/designs`, Python bindings and tests under `python`, and standalone examples under `tutorials/tutorial_smt`.

## Dependencies

SMT depends directly on:

- [ariadne-cps/configuration](https://github.com/ariadne-cps/configuration) (`ss/configuration`; shared CMake configuration).
- [ariadne-cps/cdcl](https://github.com/ariadne-cps/cdcl) (`ss/cdcl`; Boolean search engine).
- [ariadne-cps/symbolic](https://github.com/ariadne-cps/symbolic) (`ss/symbolic`; symbolic expressions).
- [ariadne-cps/constraint-solving](https://github.com/ariadne-cps/constraint-solving) (`ss/constraint-solving`; validated pruning).
- [ariadne-cps/equation-solving](https://github.com/ariadne-cps/equation-solving) (`ss/equation-solving`; interval Newton methods).
- [ariadne-cps/threading](https://github.com/ariadne-cps/threading) (`ss/threading`; workload scheduling and thread-management facilities).

The lower Function, Geometry, Algebra, Utility and Python Common dependencies are supplied transitively. CMake checks that common dependencies, including Configuration, Logging and Utility, are pinned to consistent commits. SMT no longer uses the old monolithic Kernel.

The Barr3 benchmark uses `SmtSolver` directly to verify the unsafe-region and Lie-derivative constraints derived from the published Barr3 2-64-64-1 neural barrier. The previous X-Taylor and other exploratory numerical profiles have been removed. No Linear Programming dependency is required.

## Build

```bash
git clone --recurse-submodules https://github.com/ariadne-cps/smt.git
cd smt
cmake -S . -B build -DCMAKE_BUILD_TYPE=Release
cmake --build build --parallel --target everything
ctest --test-dir build --output-on-failure
```

The standalone C++ tutorial is in `tutorials/tutorial_smt`, and the Python tutorial is `python/tutorials/tutorial_smt.py`. Both illustrate epsilon-SMT solving, including satisfiable and unsatisfiable bounded-real formulas and Boolean combinations.

## Python bindings

With a compatible Python development environment, the standalone build produces and installs the combined `pyariadne` extension, containing the Symbolic, CDCL, Constraint Solving, Equation Solving and SMT bindings and their transitive dependencies. The SMT classes are exposed as `SmtSolver`, `SmtSolverConfiguration` and `SmtResult`; `pyariadne-smt` is an internal CMake target, not a separate Python module.

## Contribution guidelines

If you would like to contribute to Ariadne SMT, please contact the developer:

- Luca Geretti <luca.geretti@univr.it>

## License

Ariadne SMT is released under the GNU General Public License v3.0.
