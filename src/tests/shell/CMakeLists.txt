add_executable(shell_test shell.cpp $<TARGET_OBJECTS:shell_js>)
target_link_libraries(shell_test leanstatic)

if(EMSCRIPTEN)
    file(WRITE ${CMAKE_CURRENT_BINARY_DIR}/shell_test
            "#!/bin/sh\nnode --stack_size=8192 ${CMAKE_CURRENT_BINARY_DIR}/shell_test.js \"$@\"\n")
    execute_process(COMMAND chmod +x ${CMAKE_CURRENT_BINARY_DIR}/shell_test)
endif()

add_test(NAME "emscripten_test"
         WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/tests/shell"
         COMMAND bash "${LEAN_SOURCE_DIR}/tests/shell/test.sh" "${CMAKE_CURRENT_BINARY_DIR}/shell_test")
