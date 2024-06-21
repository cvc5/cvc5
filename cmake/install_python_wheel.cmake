set(UNREPAIRED_WHEEL_DIR ${CMAKE_BINARY_DIR}/unrepaired-wheel)
set(REPAIRED_WHEEL_DIR ${CMAKE_BINARY_DIR}/repaired-wheel)

execute_process(COMMAND
  ${CMAKE_COMMAND} -E remove_directory ${UNREPAIRED_WHEEL_DIR} ${REPAIRED_WHEEL_DIR})

execute_process(COMMAND 
    ${Python_EXECUTABLE} -m pip wheel ${CMAKE_BINARY_DIR}/src/api/python 
    --wheel-dir=${CMAKE_BINARY_DIR}/unrepaired-wheel)

file(GLOB WHL_FILE ${UNREPAIRED_WHEEL_DIR}/cvc5*.whl)

execute_process(COMMAND
    ${Repairwheel_EXECUTABLE} -o ${CMAKE_BINARY_DIR}/repaired-wheel
    -l ${CMAKE_BINARY_DIR}/src -l ${CMAKE_BINARY_DIR}/src/parser 
    -l ${DEPS_BASE}/bin ${WHL_FILE})

file(GLOB WHL_FILE ${REPAIRED_WHEEL_DIR}/cvc5*.whl)

string(REPLACE "\"" "" INSTALL_CMD "${INSTALL_CMD}")
set(INSTALL_CMD "${INSTALL_CMD} ${WHL_FILE}")
separate_arguments(INSTALL_CMD)

execute_process(COMMAND ${INSTALL_CMD})
