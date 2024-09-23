use std::{fs, env, path::PathBuf};

fn main() -> Result<(), Box<dyn std::error::Error>> {
	let cvc5_include_dir = env::var("CVC5_INCLUDE_DIR").expect("Include directory must be present");
	let cvc5_generated_include_dir =
		env::var("CVC5_GENERATED_INCLUDE_DIR").expect("Generated include directory must be present");
	let cvc5_lib_dir = env::var("CVC5_LIB_DIR").expect("Library directory must be present");

	/*
	cxx_build::bridge("src/lib.rs")
		.std("c++17")
		.include(cvc5_include_dir.clone())
		.include(cvc5_generated_include_dir.clone())
		.include("src")
		//.flag("-isystem")
		//.flag(&cvc5_include_dir)
		.compile("cvc5-rust");
	*/

	println!("cargo:rerun-if-changed={cvc5_include_dir}/cvc5/c/cvc5.h");
	println!("cargo:rerun-if-changed={cvc5_include_dir}/cvc5/cvc5_kind.h");
	println!("cargo:rerun-if-changed={cvc5_include_dir}/cvc5/cvc5_parser.h");
	println!("cargo:rerun-if-changed={cvc5_include_dir}/cvc5/cvc5_skolem_id.h");
	println!("cargo:rerun-if-changed={cvc5_include_dir}/cvc5/cvc5_types.h");
	println!("cargo:rerun-if-changed={cvc5_generated_include_dir}/cvc5/cvc5_proof_rule.h");
	//println!("cargo:rerun-if-changed={cvc5_include_dir}/cvc5/cvc5.h");
	//println!("cargo:rerun-if-changed={cvc5_generated_include_dir}/cvc5/cvc5_export.h");

	println!("cargo:rustc-link-search={cvc5_lib_dir}");

	eprintln!("Generating bindgen...");

	let output_path = PathBuf::from(env::var("OUT_DIR").expect("OUT_DIR must be present"));
	let bindings = bindgen::Builder::default()
		.clang_arg(format!("-I{cvc5_include_dir}"))
		.clang_arg(format!("-I{cvc5_generated_include_dir}"))
		.header(format!("{cvc5_include_dir}/cvc5/c/cvc5.h"))
		.parse_callbacks(Box::new(bindgen::CargoCallbacks::new()))
		.generate()?;

	let proto_path = output_path.join("cvc5-native.rs");
	bindings.write_to_file(&proto_path)?;

	let content = fs::read_to_string(proto_path).expect("Proto file doesn't exist");
	let content = cvc5generator::transform_c_bridge(content);
	fs::write(output_path.join("cvc5.rs"), content).expect("Unable to write file");

	Ok(())
}
