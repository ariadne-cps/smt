if(NOT TARGET symbolic)
    ensure_submodule_initialized(symbolic)
    add_subdirectory(symbolic)
endif()

if(NOT TARGET cdcl)
    ensure_submodule_initialized(cdcl)
    add_subdirectory(cdcl)
endif()

if(NOT TARGET constraint_solving)
    ensure_submodule_initialized(constraint-solving)
    add_subdirectory(constraint-solving)
endif()

if(NOT TARGET equation_solving)
    ensure_submodule_initialized(equation-solving)
    add_subdirectory(equation-solving)
endif()
