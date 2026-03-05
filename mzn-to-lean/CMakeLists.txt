cmake_minimum_required(VERSION 3.16)
project(mzn2lean LANGUAGES CXX)

set(LIBMZN_SOURCE_DIR "${CMAKE_SOURCE_DIR}/libminizinc")

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# Set default build type to Release if not specified
if(NOT CMAKE_BUILD_TYPE)
    set(CMAKE_BUILD_TYPE Release CACHE STRING "Build type" FORCE)
endif()

# Configure debug and release flags
set(CMAKE_CXX_FLAGS_DEBUG "-g -O0 -DDEBUG -Wall -Wextra")
set(CMAKE_CXX_FLAGS_RELEASE "-O3 -DNDEBUG")

add_executable(mzn2lean src/main.cpp)

add_subdirectory("${LIBMZN_SOURCE_DIR}" libminizinc-build)

# Add include directories for libminizinc
target_include_directories(mzn2lean PRIVATE 
    "${LIBMZN_SOURCE_DIR}/include"
    "${CMAKE_BINARY_DIR}/libminizinc-build/include"
)

if (TARGET libminizinc::libminizinc)
target_link_libraries(mzn2lean PRIVATE libminizinc::libminizinc)
else()
target_link_libraries(mzn2lean PRIVATE mzn)
endif()
