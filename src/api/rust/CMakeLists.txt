if(("Debug" STREQUAL ${CMAKE_BUILD_TYPE}) OR ("Testing" STREQUAL ${CMAKE_BUILD_TYPE}))
    set(RUST_PROFILE debug CACHE INTERNAL "")
    set(RUST_CARGO_FLAGS)
else()
    set(RUST_PROFILE release CACHE INTERNAL "")
    set(RUST_CARGO_FLAGS --release)
endif()
set(RUST_API_OUTPUT
    ${CMAKE_CURRENT_BINARY_DIR}/${RUST_PROFILE}/libcvc5_sys.d
    ${CMAKE_CURRENT_BINARY_DIR}/${RUST_PROFILE}/libcvc5_sys.rlib
)
message("Profile: ${RUST_PROFILE}")
message(${RUST_API_OUTPUT})
set(RUST_DOC_OUTPUT
    ${CMAKE_CURRENT_BINARY_DIR}/doc/cvc5_sys/index.html
)
set(RUST_MANIFEST ${CMAKE_CURRENT_LIST_DIR}/Cargo.toml)
set(RUST_FILES
    ${CMAKE_CURRENT_LIST_DIR}/Cargo.lock
    ${CMAKE_CURRENT_LIST_DIR}/Cargo.toml
    ${CMAKE_CURRENT_LIST_DIR}/cvc5/Cargo.toml
    ${CMAKE_CURRENT_LIST_DIR}/cvc5/src/lib.rs
    ${CMAKE_CURRENT_LIST_DIR}/cvc5generator/Cargo.toml
    ${CMAKE_CURRENT_LIST_DIR}/cvc5generator/src/lib.rs
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
        cargo build ${RUST_CARGO_FLAGS} --package cvc5-sys --manifest-path=${RUST_MANIFEST}
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
        cargo doc ${RUST_CARGO_FLAGS} --package cvc5-sys --manifest-path=${RUST_MANIFEST}
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
