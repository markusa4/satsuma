cmake_minimum_required(VERSION 3.5)
project(satsuma)

include(ExternalProject)

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

ExternalProject_Add(dejavu
    GIT_REPOSITORY https://github.com/markusa4/dejavu
    GIT_TAG origin/main
    INSTALL_COMMAND ""
    CONFIGURE_COMMAND ""
    BUILD_COMMAND ""
)

add_compile_options("-O3")
add_compile_options("-Wall")
add_compile_options("-march=native")
#add_definitions(-g)
add_definitions(-DNDEBUG)
#add_definitions(-DDEJ_DEBUG)

add_executable(satsuma satsuma.cpp)
add_dependencies(satsuma dejavu)
