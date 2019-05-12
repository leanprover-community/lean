add_library(sexpr OBJECT sexpr.cpp sexpr_fn.cpp format.cpp options.cpp
  option_declarations.cpp init_module.cpp)
if(EMSCRIPTEN)
add_dependencies(sexpr gmp)
endif()
