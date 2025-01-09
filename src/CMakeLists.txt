set (CMAKE_CXX_STANDARD 20)

find_package(LLVM REQUIRED CONFIG)
find_package(Z3 REQUIRED CONFIG HINTS /opt/homebrew/Cellar/z3)
find_package(Boost REQUIRED)

message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")
message(STATUS "Using Z3.cmake in: ${Z3_DIR}")
# message(STATUS "Using Z3.cmake in: ${Z3_CXX_INCLUDE_DIRS}")

# Set your project compile flags.
# E.g. if using the C++ header files
# you will need to enable C++11 support
# for your compiler.

include_directories(${Boost_INCLUDE_DIRS})
include_directories(${LLVM_INCLUDE_DIRS})
include_directories(${Z3_CXX_INCLUDE_DIRS})
include_directories("${CMAKE_SOURCE_DIR}/include")
separate_arguments(LLVM_DEFINITIONS_LIST NATIVE_COMMAND ${LLVM_DEFINITIONS})
add_definitions(${LLVM_DEFINITIONS_LIST})

message("${CMAKE_SOURCE_DIR}/include")

# Now build our tools
add_executable(main main.cpp)
add_library(c2z3 c2z3.cpp)
add_library(rec_solver rec_solver.cpp)
add_library(smt_solver smt_solver.cpp)
add_library(loop_transformer loop_transformer.cpp)
add_library(function_summary function_summary.cpp)
add_library(value2z3 value2z3.cpp)
add_library(structures structures.cpp)
# target_compile_features(c2z3 PUBLIC cxx_std_17)


# Find the libraries that correspond to the LLVM components
# that we wish to use
llvm_map_components_to_libnames(llvm_libs core irreader analysis passes)
message(STATUS "${llvm_libs}")

# Link against LLVM libraries
target_link_libraries(main structures c2z3 value2z3 rec_solver smt_solver loop_transformer function_summary ${Z3_LIBRARIES} ${llvm_libs} )
# add_subdirectory(IfConversion)