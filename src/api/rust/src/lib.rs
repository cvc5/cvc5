#[cxx::bridge]
mod primitive {
    unsafe extern "C++" {
		 //include!(concat!(env!("CVC5_INCLUDE_DIR"), "/cvc5/cvc5.h"));
		 include!("${CVC5_INCLUDE_DIR}/cvc5/cvc5.h");
	 }
}

pub const PLACEHOLDER: &str = "placeholder";
