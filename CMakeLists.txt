
cmake_minimum_required(VERSION 3.5)
project(satsuma C CXX)

option(CLIQUES "Build with clique support" ON)

include(ExternalProject)

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(DEJAVU_LOCATION ${CMAKE_SOURCE_DIR}/src/dejavu)

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
# add_definitions(-fno-omit-frame-pointer) # for perf
add_definitions(-DNDEBUG)

# boost not required if dense logging limited
# if(POLICY CMP0167)
#    cmake_policy(SET CMP0167 NEW)
#endif()
#find_package(Boost 1.70 REQUIRED)
#INCLUDE_DIRECTORIES( ${Boost_INCLUDE_DIR} )

add_executable(satsuma src/satsuma.cpp)

if (${CLIQUES})
    add_library(cliquer_c STATIC
        src/cliquer/cliquer.c
        src/cliquer/graph.c
        src/cliquer/reorder.c
    )
    target_include_directories(cliquer_c PUBLIC src/cliquer)
    target_compile_definitions(satsuma PRIVATE CLIQUES=1)
    target_link_libraries(satsuma PRIVATE cliquer_c)
else()
    target_compile_definitions(satsuma PRIVATE CLIQUES=0)
endif()
