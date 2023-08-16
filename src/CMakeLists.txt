set (CMAKE_CXX_STANDARD 17)

find_package(LLVM REQUIRED CONFIG)
find_package(Z3 REQUIRED CONFIG HINTS /opt/homebrew/Cellar/z3)

message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")
message(STATUS "Using Z3.cmake in: ${Z3_DIR}")
# message(STATUS "Using Z3.cmake in: ${Z3_CXX_INCLUDE_DIRS}")
set (CMAKE_CXX_STANDARD 20)

# Set your project compile flags.
# E.g. if using the C++ header files
# you will need to enable C++11 support
# for your compiler.

include_directories(${LLVM_INCLUDE_DIRS})
include_directories(${Z3_CXX_INCLUDE_DIRS})
include_directories("${CMAKE_SOURCE_DIR}/include")
separate_arguments(LLVM_DEFINITIONS_LIST NATIVE_COMMAND ${LLVM_DEFINITIONS})
add_definitions(${LLVM_DEFINITIONS_LIST})


# Now build our tools
add_executable(main main.cpp)
add_library(c2z3 c2z3.cpp)
add_library(rec_solver rec_solver.cpp)
# target_compile_features(c2z3 PUBLIC cxx_std_17)


# Find the libraries that correspond to the LLVM components
# that we wish to use
llvm_map_components_to_libnames(llvm_libs core irreader analysis passes)
message(STATUS "${llvm_libs}")

# Link against LLVM libraries
target_link_libraries(main ${Z3_LIBRARIES} ${llvm_libs} c2z3 rec_solver)
# add_subdirectory(IfConversion)