#include "pybind11.hpp"

void smt_submodule(pybind11::module& module);

void smt_module(pybind11::module& module) {
    smt_submodule(module);
}
