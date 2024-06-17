set(RUST_OUTPUT
    ${CMAKE_CURRENT_BINARY_DIR}/${RUST_PROFILE}/placeholder
)
set(RUST_MANIFEST ${CMAKE_CURRENT_LIST_DIR}/Cargo.toml)
set(RUST_FILES
    ${CMAKE_CURRENT_LIST_DIR}/Cargo.lock
    ${CMAKE_CURRENT_LIST_DIR}/Cargo.toml
    ${CMAKE_CURRENT_LIST_DIR}/src/placeholder.rs
)
add_custom_command(
    OUTPUT
        ${RUST_OUTPUT}
    COMMAND
        ${CMAKE_COMMAND}
        -E env
        CARGO_TARGET_DIR=${CMAKE_CURRENT_BINARY_DIR}
        cargo build ${RUST_CARGO_FLAGS} --manifest-path=${RUST_MANIFEST} --bins
    DEPENDS
        ${RUST_FILES}
    COMMENT "Generate Rust tests"
)
add_custom_target(
    cvc5rust-test
    DEPENDS
	 cvc5rust
	 ${RUST_OUTPUT}
)
add_dependencies(build-units cvc5rust-test)

macro(cvc5_add_rust_api_test name)
  message("This test is ${CMAKE_CURRENT_BINARY_DIR}/${name}")
  add_test (NAME unit/api/rust/${name}
    COMMAND
	 	${CMAKE_CURRENT_BINARY_DIR}/${RUST_PROFILE}/${name}
  )
  set_tests_properties(unit/api/rust/${name} PROPERTIES LABELS "unit rust")
endmacro()

cvc5_add_rust_api_test(placeholder)
