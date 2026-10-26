include_directories(${Python3_INCLUDE_DIRS})

get_target_property(PYTHON_COMMON_SOURCE_DIR pyariadne-python-common SOURCE_DIR)

add_library(pyariadne-smt-submodule-obj OBJECT
    smt_submodule.cpp
)

target_include_directories(pyariadne-smt-submodule-obj PRIVATE
    "${CMAKE_CURRENT_SOURCE_DIR}"
    "${PYTHON_COMMON_SOURCE_DIR}/include"
    $<TARGET_PROPERTY:pyariadne-symbolic,INTERFACE_INCLUDE_DIRECTORIES>
)
target_link_libraries(pyariadne-smt-submodule-obj PRIVATE
    pyariadne-python-common
    pybind11::module
    smt
)
set_target_properties(pyariadne-smt-submodule-obj PROPERTIES POSITION_INDEPENDENT_CODE ON)

add_library(pyariadne-smt INTERFACE)
target_sources(pyariadne-smt INTERFACE
    $<TARGET_OBJECTS:pyariadne-smt-submodule-obj>
)
target_include_directories(pyariadne-smt INTERFACE
    $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}>
    $<TARGET_PROPERTY:pyariadne-symbolic,INTERFACE_INCLUDE_DIRECTORIES>
)
target_link_libraries(pyariadne-smt INTERFACE pyariadne-symbolic)

ariadne_add_python_module(
    NAME smt
    MODULE_SOURCE smt_module.cpp
)
