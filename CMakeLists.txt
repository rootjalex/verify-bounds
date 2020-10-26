cmake_minimum_required(VERSION 3.16)
project(verify-bounds)

set(CMAKE_CXX_STANDARD 14)
set(CMAKE_CXX_STANDARD_REQUIRED YES)
set(CMAKE_CXX_EXTENSIONS NO)

find_package(Z3 REQUIRED)
target_include_directories(z3::libz3 INTERFACE ${Z3_CXX_INCLUDE_DIRS})  # Z3 package is broken.

set(core_sources
    src/Bound.cpp
    src/Check.cpp
    src/Interval.cpp
    src/Operations.cpp)

add_library(core ${core_sources}) 
target_link_libraries(core PUBLIC z3::libz3)
target_include_directories(core PUBLIC include)

foreach (test IN ITEMS add mul sub div mod min max bitwise_and bitwise_or bitwise_not)
  add_executable(${test} checks/${test}.cpp)
  target_link_libraries(${test} PRIVATE core)
endforeach ()

foreach (bug IN ITEMS div-check mod-check)
  add_executable(${bug} bugs/${bug}.cpp)
  target_link_libraries(${bug} PRIVATE core)
endforeach ()
