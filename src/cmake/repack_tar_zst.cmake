# cmake uses a hilariously low compression level for tar.zst
# with no way to override it, so we have unpack and repack the archive

foreach(file_tar_zst "${CPACK_PACKAGE_FILES}")
  if ("${file_tar_zst}" MATCHES "^(.*\\.tar)\\.zst$")
    execute_process(COMMAND zstd -d "${file_tar_zst}" COMMAND_ERROR_IS_FATAL ANY)
    execute_process(COMMAND rm "${file_tar_zst}" COMMAND_ERROR_IS_FATAL ANY)
    execute_process(COMMAND zstd -19 "${CMAKE_MATCH_1}" COMMAND_ERROR_IS_FATAL ANY)
    execute_process(COMMAND rm "${CMAKE_MATCH_1}" COMMAND_ERROR_IS_FATAL ANY)
  endif()
endforeach()
