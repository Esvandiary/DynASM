cmake_minimum_required(VERSION 3.8)

add_subdirectory("minilua")

add_library(dynasm INTERFACE)
target_include_directories(dynasm INTERFACE "${CMAKE_CURRENT_SOURCE_DIR}/src")

set(DYNASM_SOURCE_DIR "${CMAKE_CURRENT_SOURCE_DIR}" CACHE INTERNAL "Base directory for dynasm library")
function(add_dasm_compile_command infile outfile)
    set(extra_args)
    foreach(define IN LISTS ARGN)
        list(APPEND extra_args "-D" "${define}")
    endforeach()

    add_custom_command(
        OUTPUT "${outfile}"
        COMMAND "$<TARGET_FILE:minilua>" "${DYNASM_SOURCE_DIR}/src/dynasm.lua" -o "${outfile}" ${extra_args} "${infile}"
        MAIN_DEPENDENCY "${infile}"
        VERBATIM
        USES_TERMINAL
        COMMENT "Preprocessing DynASM source file ${infile} ...")
endfunction()


if (BUILD_TESTING)
    add_dasm_compile_command("${CMAKE_CURRENT_SOURCE_DIR}/test/test.dasc" "${CMAKE_CURRENT_BINARY_DIR}/test.c")
    add_executable(dasm_test "${CMAKE_CURRENT_BINARY_DIR}/test.c")
    target_link_libraries(dasm_test dynasm)
endif ()