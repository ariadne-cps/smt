set(Python3_FIND_VIRTUALENV FIRST)
set(Python3_FIND_STRATEGY LOCATION)
set(PYBIND11_FINDPYTHON ON)

find_package(Python3 3.11 COMPONENTS Interpreter Development.Module)

option(PYTHON_ENFORCE_TESTS "Enforce Python tests" OFF)

if(Python3_FOUND)
    report_python_configuration_once()

    if(NOT TARGET pyariadne-symbolic)
        message(FATAL_ERROR "The Symbolic Python binding target is required to build pyariadne-smt.")
    endif()
    if(NOT TARGET pyariadne-cdcl)
        message(FATAL_ERROR "The CDCL Python binding target is required to build pyariadne-smt.")
    endif()
    if(NOT TARGET pyariadne-constraint_solving)
        message(FATAL_ERROR "The Constraint Solving Python binding target is required to build pyariadne-smt.")
    endif()
    if(NOT TARGET pyariadne-equation_solving)
        message(FATAL_ERROR "The Equation Solving Python binding target is required to build pyariadne-smt.")
    endif()

    add_subdirectory(bindings)

    if(CMAKE_SOURCE_DIR STREQUAL PROJECT_SOURCE_DIR)
        ariadne_finalize_python_module(NAME smt)

        # The interface binding targets contribute objects to the combined
        # pyariadne extension. Install the extension within the chosen prefix.
        if(WIN32)
            set(_python_install_dir "Lib/site-packages")
        else()
            set(_python_install_dir "lib/python${Python3_VERSION_MAJOR}.${Python3_VERSION_MINOR}/site-packages")
        endif()
        set(PYTHON_BINDINGS_INSTALL_DIR "${_python_install_dir}"
            CACHE STRING "Install destination for Python targets relative to the prefix")
        install(TARGETS pyariadne DESTINATION "${PYTHON_BINDINGS_INSTALL_DIR}")

        add_subdirectory(tests)
        add_dependencies(bindings pyariadne)
    endif()
else()
    if(PYTHON_ENFORCE_TESTS)
        message(FATAL_ERROR "Python >= 3.11 with Interpreter and Development.Module components is required when PYTHON_ENFORCE_TESTS=ON.")
    else()
        message(STATUS "Compatible Python development environment not found: Python bindings will not be built.")
    endif()
endif()
