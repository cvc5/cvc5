if(("Debug" STREQUAL ${CMAKE_BUILD_TYPE}) OR ("Testing" STREQUAL ${CMAKE_BUILD_TYPE}))
    set(RUST_PROFILE debug)
else()
    set(RUST_PROFILE release)
endif()
set(RUST_OUTPUT
    ${CMAKE_CURRENT_BINARY_DIR}/${RUST_PROFILE}/libcvc5_sys.d
    ${CMAKE_CURRENT_BINARY_DIR}/${RUST_PROFILE}/libcvc5_sys.rlib
)
set(RUST_MANIFEST ${CMAKE_CURRENT_LIST_DIR}/Cargo.toml)
set(RUST_FILES
    ${CMAKE_CURRENT_LIST_DIR}/Cargo.lock
    ${CMAKE_CURRENT_LIST_DIR}/Cargo.toml
    ${CMAKE_CURRENT_LIST_DIR}/build.rs
    ${CMAKE_CURRENT_LIST_DIR}/src/lib.rs
)
add_custom_command(
    OUTPUT
        ${RUST_OUTPUT}
    COMMAND
        ${CMAKE_COMMAND} -E env CARGO_TARGET_DIR=${CMAKE_CURRENT_BINARY_DIR}
        cargo build --${RUST_PROFILE} --manifest-path=${RUST_MANIFEST}
    DEPENDS
        ${RUST_FILES}
    COMMENT "Generate Rust API"
)
add_custom_target(
    cvc5rust
    DEPENDS
    ${RUST_OUTPUT}
)
