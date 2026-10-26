add_library(SMT_SRC OBJECT
    smt_solver.cpp
    smt_boolean.cpp
    smt_theory.cpp
)

target_include_directories(SMT_SRC PRIVATE
    "${PROJECT_SOURCE_DIR}/include/smt"
)
