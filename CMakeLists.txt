cmake_minimum_required(VERSION 3.18)
project(llvm)

add_subdirectory(tasks/dead-code-elimination)
add_subdirectory(tasks/memory-safety)
