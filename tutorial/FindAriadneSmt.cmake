find_library(ARIADNE_SMT_LIBRARY NAMES ariadne-smt)
find_path(ARIADNE_SMT_INCLUDE_DIR ariadne-smt.hpp
          PATH_SUFFIXES ariadne-smt)

find_package(Threads REQUIRED)

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(AriadneSmt DEFAULT_MSG
    ARIADNE_SMT_LIBRARY
    ARIADNE_SMT_INCLUDE_DIR
)

if(AriadneSmt_FOUND)
    get_filename_component(ARIADNE_SMT_INCLUDE_PARENT_DIR
        "${ARIADNE_SMT_INCLUDE_DIR}" DIRECTORY)
    if(NOT TARGET AriadneSmt::ariadne-smt)
        add_library(AriadneSmt::ariadne-smt UNKNOWN IMPORTED)
        set_target_properties(AriadneSmt::ariadne-smt PROPERTIES
            IMPORTED_LOCATION "${ARIADNE_SMT_LIBRARY}"
            INTERFACE_INCLUDE_DIRECTORIES
                "${ARIADNE_SMT_INCLUDE_PARENT_DIR};${ARIADNE_SMT_INCLUDE_DIR}"
            INTERFACE_LINK_LIBRARIES "Threads::Threads"
        )
    endif()
endif()
