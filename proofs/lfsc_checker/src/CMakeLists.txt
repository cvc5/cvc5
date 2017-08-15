set(lfsc_src_files
    check.cpp
    code.cpp
    expr.cpp
    lfscc.cpp
    libwriter.cpp
    print_smt2.cpp
    scccode.cpp
    sccwriter.cpp
    trie.cpp)

add_library (objlib OBJECT ${lfsc_src_files})
set_property (TARGET objlib PROPERTY POSITION_INDEPENDENT_CODE ON)

add_executable (lfsc_checker $<TARGET_OBJECTS:objlib> main.cpp)
install (TARGETS lfsc_checker
  DESTINATION "${CMAKE_INSTALL_PREFIX}/bin"
)

#add_library (liblfsc_checker SHARED $<TARGET_OBJECTS:objlib>)
#set_target_properties (liblfsc_checker PROPERTIES
#  OUTPUT_NAME lfscc
#  PUBLIC_HEADER "${CMAKE_CURRENT_SOURCE_DIR}/lfscc.h"  
#)
#install (TARGETS liblfsc_checker
#  LIBRARY DESTINATION "${CMAKE_INSTALL_PREFIX}/lib"
#  PUBLIC_HEADER DESTINATION "${CMAKE_INSTALL_PREFIX}/include"
#)

add_library (liblfsc_checker STATIC $<TARGET_OBJECTS:objlib>)
set_target_properties (liblfsc_checker PROPERTIES
  OUTPUT_NAME lfscc
  PUBLIC_HEADER "${CMAKE_CURRENT_SOURCE_DIR}/lfscc.h"  
)
install (TARGETS liblfsc_checker
  ARCHIVE DESTINATION "${CMAKE_INSTALL_PREFIX}/lib"
  PUBLIC_HEADER DESTINATION "${CMAKE_INSTALL_PREFIX}/include"
)

target_link_libraries(lfsc_checker ${LIBRARIES})

