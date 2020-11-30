# These CORE_PLFs are combined to give a "master signature" against which
# proofs are checked internally when using --check-proofs. To add support for
# more theories, just list them here in the same order you would to the LFSC
# proof-checker binary.

set(core_signature_files
    sat.plf
    er.plf
    smt.plf
    th_base.plf
    lrat.plf
    drat.plf
    th_arrays.plf
    th_bv.plf
    th_bv_bitblast.plf
    th_bv_rewrites.plf
    th_real.plf
    th_int.plf
    th_lira.plf
)

set(CORE_SIGNATURES "")

foreach(f ${core_signature_files})
  file(READ ${f} tmp)
  set(CORE_SIGNATURES "${CORE_SIGNATURES}\n${tmp}")
endforeach(f)

string(REPLACE "\\" "\\\\" CORE_SIGNATURES "${CORE_SIGNATURES}")
string(REPLACE "\"" "\\\"" CORE_SIGNATURES "${CORE_SIGNATURES}")
string(REPLACE "\n" "\\n\\\n" CORE_SIGNATURES "${CORE_SIGNATURES}")

configure_file(
  ${CMAKE_CURRENT_SOURCE_DIR}/signatures.cpp.in
  ${CMAKE_CURRENT_BINARY_DIR}/signatures.cpp)

libcvc4_add_sources(GENERATED signatures.cpp)
install(FILES ${core_signature_files} DESTINATION share/cvc4)
