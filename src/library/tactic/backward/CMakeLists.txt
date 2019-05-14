add_library(backward OBJECT init_module.cpp backward_lemmas.cpp backward_chaining.cpp)
if(EMSCRIPTEN)
add_dependencies(backward gmp)
endif()