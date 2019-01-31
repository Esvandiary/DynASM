cmake_minimum_required(VERSION 3.8)

add_subdirectory("minilua")

add_library(dynasm INTERFACE)
target_include_directories(dynasm INTERFACE "${CMAKE_CURRENT_SOURCE_DIR}/src")

function(add_dasm_compile_command infile outfile arch)
	add_custom_command(
		OUTPUT "${outfile}"
		COMMAND "$<TARGET_FILE:minilua>" "dynasm.lua" -o "${outfile}" -D "${arch}" "${infile}"
		MAIN_DEPENDENCY "${infile}"
		WORKING_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/dynasm"
		VERBATIM
		COMMENT "Preprocessing DynASM source file ${infile} ...")
endfunction()
