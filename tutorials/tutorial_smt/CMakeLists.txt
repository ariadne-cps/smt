cmake_minimum_required(VERSION 3.15)
project(AriadneSmtTutorial LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

list(APPEND CMAKE_MODULE_PATH "${CMAKE_CURRENT_SOURCE_DIR}")
find_package(AriadneSmt REQUIRED)

add_executable(tutorial_smt tutorial_smt.cpp)
target_link_libraries(tutorial_smt PRIVATE AriadneSmt::ariadne-smt)
