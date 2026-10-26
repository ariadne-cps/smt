# Ariadne Satisfiability

[![License: GPL v3](https://img.shields.io/badge/License-GPL%20v3-blue.svg)](https://www.gnu.org/licenses/gpl-3.0)
[![Unix Status](https://github.com/ariadne-cps/satisfiability/actions/workflows/unix.yml/badge.svg)](https://github.com/ariadne-cps/satisfiability/actions/workflows/unix.yml)
[![Windows Status](https://github.com/ariadne-cps/satisfiability/actions/workflows/win.yml/badge.svg)](https://github.com/ariadne-cps/satisfiability/actions/workflows/win.yml)
[![Sanitizers Status](https://github.com/ariadne-cps/satisfiability/actions/workflows/sanitizers.yml/badge.svg)](https://github.com/ariadne-cps/satisfiability/actions/workflows/sanitizers.yml)
[![Coverage Status](https://github.com/ariadne-cps/satisfiability/actions/workflows/coverage.yml/badge.svg)](https://github.com/ariadne-cps/satisfiability/actions/workflows/coverage.yml)
[![codecov](https://codecov.io/gh/ariadne-cps/satisfiability/branch/main/graph/badge.svg)](https://codecov.io/gh/ariadne-cps/satisfiability)

Ariadne Satisfiability is the standalone C++20 bounded real satisfiability layer used by Ariadne. It provides epsilon-SMT solving, Boolean and theory reasoning, validated satisfiability checks and benchmark support on top of Ariadne Symbolic.

## Layout

Public headers live under `include/satisfiability`, implementations under `src`, C++ tests under `tests`, benchmarks under `benchmarks`, Python bindings and tests under `python`, design documentation under `doc`, and standalone examples under `tutorials`.

The umbrella header is `include/ariadne-satisfiability.hpp`.

## Dependencies

Satisfiability depends directly on:

- [ariadne-cps/symbolic](https://github.com/ariadne-cps/symbolic), included as a Git submodule.
- [ariadne-cps/configuration](https://github.com/ariadne-cps/configuration), used for shared build configuration.

Symbolic supplies the symbolic-expression layer and the lower Ariadne Kernel stack transitively, together with their external dependencies.

## Build

```bash
git clone --recurse-submodules https://github.com/ariadne-cps/satisfiability.git
cd satisfiability
cmake -S . -B build -DCMAKE_BUILD_TYPE=Release
cmake --build build --parallel --target everything
ctest --test-dir build --output-on-failure
```

## Python bindings

When a compatible Python development environment is available, the standalone build produces `pyariadne` from the Symbolic bindings plus the Satisfiability bindings.

## Contribution guidelines

If you would like to contribute to Ariadne Satisfiability, please contact the developer:

- Luca Geretti <luca.geretti@univr.it>

## License

Ariadne Satisfiability is released under the GNU General Public License v3.0.
