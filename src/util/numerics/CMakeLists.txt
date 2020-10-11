add_library(numerics OBJECT mpz.cpp mpq.cpp)
if(EMSCRIPTEN)
add_dependencies(numerics gmp)
endif()
