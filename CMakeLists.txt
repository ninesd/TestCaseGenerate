cmake_minimum_required(VERSION 2.8.8)
project(TestCaseGenerate)

# Allow the user to override the install prefix.
if(NOT DEFINED CMAKE_INSTALL_PREFIX)
    set(CMAKE_INSTALL_PREFIX "/usr/local")
endif()
string(REGEX REPLACE "/$" "" CMAKE_INSTALL_PREFIX "${CMAKE_INSTALL_PREFIX}")

# Set your project compile flags.
# E.g. if using the C++ header files
# you will need to enable C++11 support
# for your compiler.
SET( CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++11")
add_compile_options(-fexceptions)


find_package(LLVM REQUIRED CONFIG)

if (LLVM_FOUND)
    message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
    message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")
    include_directories(${LLVM_INCLUDE_DIRS})
    link_directories(${LLVM_LIBRARY_DIRS})
    add_definitions(${LLVM_DEFINITIONS})
else()
    message(WARNING "LLVM not found.")
endif()

SET(CMAKE_INCLUDE_PATH "/usr/local/include" ${CMAKE_INCLUDE_PATH})
SET(CMAKE_LIBRARY_PATH "/usr/local/lib" ${CMAKE_INCLUDE_PATH})

find_package(Boost)

if(Boost_FOUND)
    message(STATUS "boost include path is : ${Boost_INCLUDE_DIRS}")
    message(STATUS "boost library path is : ${Boost_LIBRARY_DIRS}")
    message(STATUS "boost libraries is : ${Boost_LIBRARIES}")
    include_directories("/usr/local/include/boost")
    link_directories("/usr/local/lib/boost")
else()
    message(WARNING "boost not found.")
endif()

# Now build our tools
add_executable(TestCaseGenerate TestCaseGenerate.cpp)

# Find the libraries that correspond to the LLVM components
# that we wish to use
llvm_map_components_to_libnames(llvm_libs x86asmparser bitreader support mc option profiledata)
message(STATUS "LLVM_LIBS: ${llvm_libs}")

target_link_libraries(TestCaseGenerate
        clangFrontend
        clangSerialization
        clangDriver
        clangTooling
        clangParse
        clangSema
        clangAnalysis
        clangRewriteFrontend
        clangRewrite
        clangEdit
        clangAST
        clangLex
        clangBasic
        clangASTMatchers
        )

target_link_libraries(TestCaseGenerate ${llvm_libs} boost_filesystem boost_system boost_regex)

target_link_libraries(TestCaseGenerate boost_filesystem boost_system boost_regex)

execute_process(COMMAND bash "-c" "llvm-config --cxxflags" OUTPUT_VARIABLE compile_flags OUTPUT_STRIP_TRAILING_WHITESPACE)
set_property(TARGET TestCaseGenerate APPEND PROPERTY COMPILE_FLAGS "${compile_flags} -Wno-strict-aliasing")

install(TARGETS TestCaseGenerate DESTINATION bin)
