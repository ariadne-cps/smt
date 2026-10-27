include(CTest)

set(UNIT_TESTS
    test_smt_solver
    test_smt_neural_benchmarks
    test_smt_boolean
    test_smt_theory
    test_smt_cdcl_core
)
foreach(TEST ${UNIT_TESTS})
    add_executable(${TEST} ${TEST}.cpp)
    target_link_libraries(${TEST} ariadne-smt smt)
    add_test(NAME ${TEST} COMMAND $<TARGET_FILE:${TEST}>)
    set_property(TEST ${TEST} PROPERTY LABELS "smt")
endforeach()
target_include_directories(test_smt_cdcl_core PRIVATE ${PROJECT_SOURCE_DIR}/src)
target_include_directories(test_smt_neural_benchmarks PRIVATE ${PROJECT_SOURCE_DIR}/benchmarks)
target_compile_definitions(test_smt_neural_benchmarks PRIVATE
    ARIADNE_SMT_BARR3_DATA_PATH="${PROJECT_SOURCE_DIR}/benchmarks/data/smt_barr3_full64.bin")
add_custom_target(tests)
add_dependencies(tests ${UNIT_TESTS})
