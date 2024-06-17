if(("Debug" STREQUAL ${CMAKE_BUILD_TYPE}) OR ("Testing" STREQUAL ${CMAKE_BUILD_TYPE}))
    set(RUST_PROFILE debug PARENT_SCOPE)
    set(RUST_CARGO_FLAGS PARENT_SCOPE)
else()
    set(RUST_PROFILE release PARENT_SCOPE)
    set(RUST_CARGO_FLAGS --release PARENT_SCOPE)
endif()
set(RUST_API_OUTPUT
    ${CMAKE_CURRENT_BINARY_DIR}/${RUST_PROFILE}/libcvc5_sys.d
    ${CMAKE_CURRENT_BINARY_DIR}/${RUST_PROFILE}/libcvc5_sys.rlib
)
set(RUST_DOC_OUTPUT
    ${CMAKE_CURRENT_BINARY_DIR}/${RUST_PROFILE}/doc
)
set(RUST_MANIFEST ${CMAKE_CURRENT_LIST_DIR}/Cargo.toml)
set(RUST_FILES
    ${CMAKE_CURRENT_LIST_DIR}/Cargo.lock
    ${CMAKE_CURRENT_LIST_DIR}/Cargo.toml
    ${CMAKE_CURRENT_LIST_DIR}/src/lib.rs
)
add_custom_command(
    OUTPUT
        ${RUST_API_OUTPUT}
    COMMAND
        ${CMAKE_COMMAND}
        -E env
        CARGO_TARGET_DIR=${CMAKE_CURRENT_BINARY_DIR}
        CVC5_INCLUDE_DIR=${PROJECT_SOURCE_DIR}/include
        CVC5_GENERATED_INCLUDE_DIR=${CMAKE_BINARY_DIR}/include
        CVC5_LIB_DIR=${CMAKE_BINARY_DIR}/src
        cargo build ${RUST_CARGO_FLAGS} --manifest-path=${RUST_MANIFEST}
    DEPENDS
        ${RUST_FILES}
    COMMENT "Generate Rust API"
)
add_custom_command(
    OUTPUT
        ${RUST_DOC_OUTPUT}
    COMMAND
        ${CMAKE_COMMAND}
        -E env
        CARGO_TARGET_DIR=${CMAKE_CURRENT_BINARY_DIR}
        CVC5_INCLUDE_DIR=${PROJECT_SOURCE_DIR}/include
        CVC5_GENERATED_INCLUDE_DIR=${CMAKE_BINARY_DIR}/include
        CVC5_LIB_DIR=${CMAKE_BINARY_DIR}/src
        cargo doc ${RUST_CARGO_FLAGS} --manifest-path=${RUST_MANIFEST}
    DEPENDS
        ${RUST_FILES}
    COMMENT "Generate Rust API Documentation"
)
add_custom_target(
    cvc5rust
    DEPENDS
    ${RUST_API_OUTPUT}
    ${RUST_DOC_OUTPUT}
)
