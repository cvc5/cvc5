use quote;
use syn::{AttrStyle, Attribute, Expr, ExprLit, File, ForeignItem, Item, Lit, Meta, MetaNameValue};

fn extract_doc(attr: &Attribute) -> String
{
	let Attribute {
		style: AttrStyle::Outer,
		meta: Meta::NameValue(MetaNameValue { path, value, .. }),
		..
	} = attr
	else {
		panic!("This is not a doc attribute")
	};
	let Some(key) = path.get_ident() else {
		panic!("Not a doc attribute, but {path:?}");
	};
	if key.to_string() != "doc" {
		panic!("Not a doc, but {path:?}");
	}
	let Expr::Lit(ExprLit {
		lit: Lit::Str(doc), ..
	}) = value
	else {
		panic!("Doc value wrong");
	};
	doc.value()
}

fn generate_safe_bindings(file: &File) -> File
{
	for item in file.items.iter() {
		let Item::ForeignMod(data) = item else {
			continue;
		};
		let [fitem] = &data.items[..] else {
			panic!("Extern block should only have one item");
		};
		let ForeignItem::Fn(fndata) = fitem else {
			panic!("Not foreign item");
		};
		let doc = extract_doc(&fndata.attrs[0]);
		println!("cargo:warning={}", &doc[..50]);
		println!("cargo:warning={:?}", fndata.sig.ident);
	}
	let items = vec![];
	File {
		shebang: None,
		attrs: vec![],
		items,
	}
}

pub fn transform_c_bridge(code: String) -> String
{
	let native_file = syn::parse_file(&code).expect("Generated file should be valid rust");
	let binding_file = generate_safe_bindings(&native_file);
	quote!(#binding_file).to_string()
}
