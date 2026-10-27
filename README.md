# Ariadne SMT

[![License: GPL v3](https://img.shields.io/badge/License-GPL%20v3-blue.svg)](https://www.gnu.org/licenses/gpl-3.0)
[![Unix Status](https://github.com/ariadne-cps/smt/actions/workflows/unix.yml/badge.svg)](https://github.com/ariadne-cps/smt/actions/workflows/unix.yml)
[![Windows Status](https://github.com/ariadne-cps/smt/actions/workflows/win.yml/badge.svg)](https://github.com/ariadne-cps/smt/actions/workflows/win.yml)
[![Sanitizers Status](https://github.com/ariadne-cps/smt/actions/workflows/sanitizers.yml/badge.svg)](https://github.com/ariadne-cps/smt/actions/workflows/sanitizers.yml)
[![Coverage Status](https://github.com/ariadne-cps/smt/actions/workflows/coverage.yml/badge.svg)](https://github.com/ariadne-cps/smt/actions/workflows/coverage.yml)
[![codecov](https://codecov.io/gh/ariadne-cps/smt/branch/main/graph/badge.svg)](https://codecov.io/gh/ariadne-cps/smt)

Ariadne SMT is the standalone C++20 **epsilon-SMT solver for bounded real constraints** in Ariadne. It combines Boolean reasoning with validated real-constraint evaluation, interval-based pruning and subdivision to search for epsilon-satisfying witnesses or establish unsatisfiability when possible. Results distinguish **UNSAT**, **EPSILON_SAT** and **UNKNOWN**; an unknown result must not be interpreted as satisfiability or unsatisfiability.

This repository is dedicated to the epsilon-SMT solver. General-purpose symbolic expressions belong to [Ariadne Symbolic](https://github.com/ariadne-cps/symbolic), and numerical and geometric algorithms belong to [Ariadne Kernel](https://github.com/ariadne-cps/kernel). The benchmarks here evaluate the epsilon-SMT solver and its internal theory-reasoning strategies rather than exposing separate general-purpose solver products.

## Layout

The public API lives in `include/smt`, with umbrella header `include/ariadne-smt.hpp`. The solver implementation is under `src`, the C++ regression suite under `tests`, performance and solver-strategy benchmarks under `benchmarks`, the design journal under `doc/designs`, Python bindings and tests under `python`, and standalone examples under `tutorials/tutorial_smt`.

## Dependencies

SMT depends directly on:

- [ariadne-cps/symbolic](https://github.com/ariadne-cps/symbolic) (Git submodule).
- [ariadne-cps/configuration](https://github.com/ariadne-cps/configuration) (shared build configuration).
- [ariadne-cps/cdcl](https://github.com/ariadne-cps/cdcl) (shared Boolean search engine).

Symbolic brings in Kernel and the lower Ariadne dependencies transitively.
SMT checks that the transitive Utility commit matches the one pinned by CDCL.

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

With a compatible Python development environment, the standalone build produces and installs the combined `pyariadne` extension, containing the Kernel, Symbolic and SMT bindings. The SMT classes are exposed as `SmtSolver`, `SmtSolverConfiguration` and `SmtResult`; `pyariadne-smt` is an internal CMake target, not a separate Python module.

## Contribution guidelines

If you would like to contribute to Ariadne SMT, please contact the developer:

- Luca Geretti <luca.geretti@univr.it>

## License

Ariadne SMT is released under the GNU General Public License v3.0.
