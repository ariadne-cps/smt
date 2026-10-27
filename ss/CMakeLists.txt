if(NOT TARGET symbolic)
    ensure_submodule_initialized(symbolic)
    add_subdirectory(symbolic)
endif()

if(NOT TARGET cdcl)
    ensure_submodule_initialized(cdcl)
    add_subdirectory(cdcl)
endif()
