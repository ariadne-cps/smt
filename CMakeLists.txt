cmake_minimum_required(VERSION 3.15)

project(Smt VERSION 1.0)

option(WARNINGS_AS_ERRORS "Treat compiler warnings as errors" OFF)
option(BUILD_PYTHON_BINDINGS "Build Python bindings" ON)

if(NOT TARGET ariadne-build)
    find_package(Git REQUIRED)
    # Keep the initial Build checkout output in English.
    execute_process(
        COMMAND "${CMAKE_COMMAND}" -E env "LC_ALL=C"
                "${GIT_EXECUTABLE}" -C "${CMAKE_CURRENT_SOURCE_DIR}"
                submodule update --init -- ss/bui
        RESULT_VARIABLE _result)
    if(_result)
        message(FATAL_ERROR "Cannot initialize build submodule")
    endif()
    include("${CMAKE_CURRENT_SOURCE_DIR}/ss/bui/cmake/ProjectOptions.cmake")
endif()

if(EXISTS "${PROJECT_SOURCE_DIR}/.git")
    # Pinned child commits guarantee their internal consistency.
    # Preserve explicit comparisons across independent dependency branches.
    require_same_dependency_commit(Build CHAINS
        "build" "cdcl|build" "symbolic|build"
        "constraint-solving|build" "equation-solving|build" "testing|build")
    require_same_dependency_commit(Function CHAINS
        "symbolic|function"
        "constraint-solving|nonlinear-programming|function"
        "equation-solving|function")
    require_same_dependency_commit(Logging CHAINS
        "symbolic|function|geometry|algebra|interval|numeric|logging"
        "cdcl|threading|logging")
    require_same_dependency_commit(PythonCommon CHAINS
        "symbolic|function|geometry|algebra|interval|numeric|foundation|python-common"
        "cdcl|python-common")
    require_same_dependency_commit(Testing CHAINS
        "testing" "cdcl|testing" "symbolic|testing"
        "constraint-solving|testing" "equation-solving|testing")
endif()

setup_project()

include_directories(${PROJECT_SOURCE_DIR}/include)

add_subdirectory(ss)

add_library(smt INTERFACE)
target_include_directories(smt INTERFACE
    $<BUILD_INTERFACE:${PROJECT_SOURCE_DIR}/include>
    $<INSTALL_INTERFACE:include/ariadne-smt>
)
target_link_libraries(smt INTERFACE symbolic cdcl constraint_solving equation_solving)

add_subdirectory(src)
target_link_libraries(SMT_SRC PRIVATE smt)

ariadne_register_public_headers(
    TARGET smt
    DIRECTORIES "${PROJECT_SOURCE_DIR}/include/smt"
    FILES "${PROJECT_SOURCE_DIR}/include/ariadne-smt.hpp"
)

setup_project_library(
    TARGET ariadne-smt
    OBJECTS SMT_SRC
    LINK_LIBRARIES smt
)

setup_standalone_project_tests(
    TARGET ariadne-smt
    TEST_DIRECTORY tests
    TEST_TARGET tests
    SOURCES
        "${PROJECT_SOURCE_DIR}/include"
        "${PROJECT_SOURCE_DIR}/src"
)

if(BUILD_PYTHON_BINDINGS)
    add_subdirectory(python)
endif()

if(CMAKE_SOURCE_DIR STREQUAL PROJECT_SOURCE_DIR)
    ariadne_install_dependency_bundle(
        TARGET smt
        DESTINATION include/ariadne-smt
    )
endif()
