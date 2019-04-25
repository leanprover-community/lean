function(add_exec_test_working name tgt)
    if(${EMSCRIPTEN})
        target_link_libraries(${tgt} "--memory-init-file 0")
        add_test(NAME ${name}
        WORKING_DIRECTORY "${LEAN_BINARY_DIR}"
        COMMAND node --stack_size=8192 ${CMAKE_CURRENT_BINARY_DIR}/${tgt}.js)
    else()
        add_test(NAME ${name}
        WORKING_DIRECTORY "${LEAN_BINARY_DIR}"
        COMMAND ${CMAKE_CURRENT_BINARY_DIR}/${tgt})
    endif()
endfunction()

add_executable(shared_test shared.cpp)
target_link_libraries(shared_test ${EXTRA_LIBS} leanshared)
add_exec_test_working(shared_test shared_test)

add_executable(c_name_test name.c)
target_link_libraries(c_name_test ${EXTRA_LIBS} leanshared)
add_exec_test_working(c_name_test c_name_test)

add_executable(c_options_test options.c)
target_link_libraries(c_options_test ${EXTRA_LIBS} leanshared)
add_exec_test_working(c_options_test c_options_test)

add_executable(c_univ_test univ.c)
target_link_libraries(c_univ_test ${EXTRA_LIBS} leanshared)
add_exec_test_working(c_univ_test c_univ_test)

add_executable(c_expr_test expr.c)
target_link_libraries(c_expr_test ${EXTRA_LIBS} leanshared)
add_exec_test_working(c_expr_test c_expr_test)

# add_executable(c_env_test env.c)
# target_link_libraries(c_env_test ${EXTRA_LIBS} leanshared)
# add_test(NAME c_env_test
#          WORKING_DIRECTORY "${LEAN_BINARY_DIR}"
#          COMMAND "${CMAKE_CURRENT_BINARY_DIR}/c_env_test")
# SET_TESTS_PROPERTIES(c_env_test
#   PROPERTIES ENVIRONMENT "LEAN_PATH=${LEAN_SOURCE_DIR}/../library")

add_executable(thread_test thread.cpp)
target_link_libraries(thread_test ${EXTRA_LIBS} leanshared)
add_exec_test_working(thread_test thread_test)
SET_TESTS_PROPERTIES(thread_test
  PROPERTIES ENVIRONMENT "LEAN_PATH=${LEAN_SOURCE_DIR}/../library")
