#[cxx::bridge(namespace = "cvc5")]
pub mod primitive {
	unsafe extern "C++" {
		include!("cvc5/cvc5.h");
		type CVC5ApiException;
		type CVC5ApiUnsupportedException;
		type Result;
	}

}
#[cxx::bridge(namespace = "cvc5::parser")]
pub mod parser {
	unsafe extern "C++" {
		include!("cvc5/cvc5_parser.h");
	}
}

pub const PLACEHOLDER: &str = "placeholder";
