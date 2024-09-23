
#[allow(non_upper_case_globals)]
#[allow(non_camel_case_types)]
#[allow(non_snake_case)]
#[allow(dead_code)]
#[allow(clippy::useless_transmute)]

// This isn't rustdoc, so it should be ok.
#[allow(rustdoc::invalid_rust_codeblocks)]
#[allow(rustdoc::invalid_html_tags)]
pub mod native {
	include!(concat!(env!("OUT_DIR"), "/cvc5-native.rs"));
}

include!(concat!(env!("OUT_DIR"), "/cvc5.rs"));
