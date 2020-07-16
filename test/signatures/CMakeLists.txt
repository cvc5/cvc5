set(lfsc_test_file_list
  drat_test.plf
  er_test.plf
  example-arrays.plf
  example.plf
  example-quant.plf
  ex_bv.plf
  ex-mem.plf
  lrat_test.plf
  th_lira_test.plf
)

set(test_script ${CMAKE_CURRENT_LIST_DIR}/run_test.py)

macro(lfsc_test file)
  set(test_name "signatures/${file}")
  add_test(
    NAME "${test_name}"
    COMMAND
      "${PYTHON_EXECUTABLE}"
      "${test_script}"
      "${LFSC_BINARY}"
      "${CMAKE_CURRENT_LIST_DIR}/${file}"
      "${CMAKE_SOURCE_DIR}/proofs/signatures"
    WORKING_DIRECTORY ${CMAKE_CURRENT_LIST_DIR}
  )

  set_tests_properties("${test_name}" PROPERTIES LABELS "signatures")
endmacro()

foreach(file ${lfsc_test_file_list})
  lfsc_test(${file})
endforeach()
