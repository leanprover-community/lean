add_executable(leanchecker checker.cpp text_import.cpp simple_pp.cpp
        ${LIB_OBJ_UTIL} $<TARGET_OBJECTS:sexpr>
        $<TARGET_OBJECTS:kernel> $<TARGET_OBJECTS:inductive> $<TARGET_OBJECTS:quotient>)
target_link_libraries(leanchecker ${EXTRA_UTIL_LIBS})
install(TARGETS leanchecker DESTINATION bin)
