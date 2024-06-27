use std::{env, path::PathBuf};

fn main() {
	let _output_path = PathBuf::from(env::var("OUT_DIR").expect("OUT_DIR must be present"));
	let cvc5_include_dir = env::var("CVC5_INCLUDE_DIR").expect("Include directory must be present");
	let cvc5_generated_include_dir =
		env::var("CVC5_GENERATED_INCLUDE_DIR").expect("Generated include directory must be present");

	cxx_build::bridge("src/lib.rs")
		.std("c++17")
		.include(cvc5_include_dir.clone())
		.include(cvc5_generated_include_dir.clone())
		//.flag("-isystem")
		//.flag(&cvc5_include_dir)
		.compile("cvc5-rust");

	println!("cargo:rerun-if-changed=src/lib.rs");
	println!("cargo:rerun-if-changed=${cvc5_include_dir}/cvc5/cvc5.h");
	println!("cargo:rerun-if-changed=${cvc5_include_dir}/cvc5/cvc5_kind.h");
	println!("cargo:rerun-if-changed=${cvc5_include_dir}/cvc5/cvc5_parser.h");
	println!("cargo:rerun-if-changed=${cvc5_include_dir}/cvc5/cvc5_skolem_id.h");
	println!("cargo:rerun-if-changed=${cvc5_include_dir}/cvc5/cvc5_types.h");
	println!("cargo:rerun-if-changed=${cvc5_generated_include_dir}/cvc5/cvc5_export.h");
	println!("cargo:rerun-if-changed=${cvc5_generated_include_dir}/cvc5/cvc5_proof_rule.h");
}
