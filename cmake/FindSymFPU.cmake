# Find SymFPU
# SymFPU_FOUND - system has SymFPU lib
# SymFPU_INCLUDE_DIR - the SymFPU include directory

find_path(SymFPU_INCLUDE_DIR NAMES symfpu/core/unpackedFloat.h)

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(SymFPU DEFAULT_MSG SymFPU_INCLUDE_DIR)

mark_as_advanced(SymFPU_INCLUDE_DIR)
