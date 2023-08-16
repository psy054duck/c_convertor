cmake_minimum_required(VERSION 3.13.4)
# project(IfConversionPass)

find_package(LLVM REQUIRED CONFIG)
find_package(Z3 REQUIRED CONFIG HINTS /opt/homebrew/Cellar/z3)
include_directories(SYSTEM ${LLVM_INCLUDE_DIRS})

#===============================================================================
# 2. LLVM-TUTOR BUILD CONFIGURATION
#===============================================================================
# Use the same C++ standard as LLVM does
set(CMAKE_CXX_STANDARD 17 CACHE STRING "")

# LLVM is normally built without RTTI. Be consistent with that.
# if(NOT LLVM_ENABLE_RTTI)
#   set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fno-rtti")
# endif()

#===============================================================================
# 3. ADD THE TARGET
#===============================================================================
add_library(IfConversion SHARED IfConversion.cpp)
include_directories("${CMAKE_CURRENT_SOURCE_DIR}/../include")

target_link_libraries(IfConversion "-undefined dynamic_lookup")
# Allow undefined symbols in shared objects on Darwin (this is the default
# behaviour on Linux)
# target_link_libraries(HelloWorld
#    "$<$<PLATFORM_ID:Darwin>:-undefined dynamic_lookup>")