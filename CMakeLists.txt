cmake_minimum_required(VERSION 3.5)
project(satsuma)

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

add_compile_options("-O3")
add_compile_options("-Wall")
add_compile_options("-march=native")
add_definitions(-g)
add_definitions(-DNDEBUG)

#add_definitions(-DDEJ_DEBUG)

add_executable(satsuma satsuma.cpp)
