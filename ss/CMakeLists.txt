if(NOT TARGET symbolic)
    ariadne_add_submodule(symbolic)
endif()

if(NOT TARGET cdcl)
    ariadne_add_submodule(cdcl)
endif()

if(NOT TARGET constraint_solving)
    ariadne_add_submodule(constraint-solving)
endif()

if(NOT TARGET equation_solving)
    ariadne_add_submodule(equation-solving)
endif()
