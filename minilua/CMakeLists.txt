cmake_minimum_required(VERSION 3.8)

add_executable(minilua "${CMAKE_CURRENT_SOURCE_DIR}/minilua.c")

if (UNIX)
    target_link_libraries(minilua PRIVATE "m")
endif ()

if (MSVC)
    target_compile_definitions(minilua PRIVATE "_CRT_SECURE_NO_WARNINGS")
endif ()