add_library(inductive_compiler OBJECT
  init_module.cpp
  compiler.cpp
  add_decl.cpp
  ginductive_decl.cpp
  ginductive.cpp
  basic.cpp
  mutual.cpp
  nested.cpp
  util.cpp
  )
if(EMSCRIPTEN)
add_dependencies(inductive_compiler gmp)
endif()