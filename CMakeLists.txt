cmake_minimum_required(VERSION 3.16)
project(verify-bounds)

set(CMAKE_CXX_STANDARD 14)
set(CMAKE_CXX_STANDARD_REQUIRED YES)
set(CMAKE_CXX_EXTENSIONS NO)

find_package(Z3 REQUIRED)
find_path(Z3_INCLUDE_DIR z3++.h)
include_directories(${Z3_INCLUDE_DIR})

set(core_sources
    src/Bound.cpp
    src/Check.cpp
    src/Interval.cpp
    src/Operations.cpp)

add_library(core ${core_sources}) 
target_link_libraries(core PUBLIC z3::libz3)
target_include_directories(core PUBLIC include)

foreach (test IN ITEMS add div-check mul sub)
  add_executable(${test} ${test}.cpp)
  target_link_libraries(${test} PRIVATE core)
endforeach ()

