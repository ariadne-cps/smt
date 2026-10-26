find_library(ARIADNE_SATISFIABILITY_LIBRARY NAMES ariadne-satisfiability)
find_path(ARIADNE_SATISFIABILITY_INCLUDE_DIR ariadne-satisfiability.hpp
          PATH_SUFFIXES ariadne-satisfiability)

find_package(Threads REQUIRED)

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(AriadneSatisfiability DEFAULT_MSG
    ARIADNE_SATISFIABILITY_LIBRARY
    ARIADNE_SATISFIABILITY_INCLUDE_DIR
)

if(AriadneSatisfiability_FOUND)
    get_filename_component(ARIADNE_SATISFIABILITY_INCLUDE_PARENT_DIR
        "${ARIADNE_SATISFIABILITY_INCLUDE_DIR}" DIRECTORY)
    if(NOT TARGET AriadneSatisfiability::ariadne-satisfiability)
        add_library(AriadneSatisfiability::ariadne-satisfiability UNKNOWN IMPORTED)
        set_target_properties(AriadneSatisfiability::ariadne-satisfiability PROPERTIES
            IMPORTED_LOCATION "${ARIADNE_SATISFIABILITY_LIBRARY}"
            INTERFACE_INCLUDE_DIRECTORIES
                "${ARIADNE_SATISFIABILITY_INCLUDE_PARENT_DIR};${ARIADNE_SATISFIABILITY_INCLUDE_DIR}"
            INTERFACE_LINK_LIBRARIES "Threads::Threads"
        )
    endif()
endif()
