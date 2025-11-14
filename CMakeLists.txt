cmake_minimum_required(VERSION 3.5)
project(satsuma)

include(ExternalProject)

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(DEJAVU_LOCATION ${CMAKE_SOURCE_DIR}/dejavu)

include(FetchContent)
FetchContent_Declare(dejavu
        GIT_REPOSITORY "https://github.com/markusa4/dejavu.git"
        GIT_TAG "origin/main"
        SOURCE_DIR ${DEJAVU_LOCATION})
FetchContent_MakeAvailable(dejavu)

add_compile_options("-O3")
add_compile_options("-Wall")
add_compile_options("-march=native")
# add_definitions(-g)
add_definitions(-DNDEBUG)

# boost required at the moment
if(POLICY CMP0167)
    cmake_policy(SET CMP0167 NEW)
endif()
find_package(Boost 1.70 REQUIRED)
INCLUDE_DIRECTORIES( ${Boost_INCLUDE_DIR} )

add_executable(satsuma satsuma.cpp)
