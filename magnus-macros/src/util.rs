use std::collections::HashMap;

use proc_macro2::Span;
use syn::{spanned::Spanned, AttributeArgs, Error, Lit, LitBool, Meta, MetaNameValue, NestedMeta};

pub trait Extract: Sized {
    fn extract(name: &str, map: &mut HashMap<String, Lit>) -> Result<Self, Error>;
}

impl Extract for String {
    fn extract(name: &str, map: &mut HashMap<String, Lit>) -> Result<Self, Error> {
        match map.remove(name) {
            Some(Lit::Str(lit_str)) => Ok(lit_str.value()),
            Some(lit) => Err(Error::new_spanned(lit, "Expected string")),
            None => Err(Error::new(
                Span::call_site(),
                format!("Missing field `{}`", name),
            )),
        }
    }
}

impl Extract for Option<String> {
    fn extract(name: &str, map: &mut HashMap<String, Lit>) -> Result<Self, Error> {
        match map.remove(name) {
            Some(Lit::Str(lit_str)) => Ok(Some(lit_str.value())),
            Some(lit) => Err(Error::new_spanned(lit, "Expected string")),
            None => Ok(None),
        }
    }
}

impl Extract for Option<bool> {
    fn extract(name: &str, map: &mut HashMap<String, Lit>) -> Result<Self, Error> {
        match map.remove(name) {
            Some(Lit::Bool(lit_bool)) => Ok(Some(lit_bool.value())),
            Some(lit) => Err(Error::new_spanned(lit, "Expected bool")),
            None => Ok(None),
        }
    }
}

pub struct Args(HashMap<String, Lit>);

impl Args {
    pub fn new(args: AttributeArgs, known: &[&str]) -> Result<Self, Error> {
        let mut map = HashMap::new();

        for nested_meta in args {
            let meta = match nested_meta {
                NestedMeta::Meta(v) => v,
                NestedMeta::Lit(_) => {
                    return Err(Error::new_spanned(nested_meta, "Unexpected literal"))
                }
            };

            let (path, lit) = match meta {
                Meta::Path(v) => {
                    let lit = Lit::Bool(LitBool::new(true, v.span()));
                    (v, lit)
                }
                Meta::List(_) => return Err(Error::new_spanned(meta, "Unexpected meta list")),
                Meta::NameValue(MetaNameValue { path, lit, .. }) => (path, lit),
            };

            if let Some(ident) = path.get_ident() {
                let s = ident.to_string();
                if !known.contains(&s.as_str()) {
                    return Err(Error::new_spanned(ident, "Unknown field"));
                }
                if map.insert(s, lit).is_some() {
                    return Err(Error::new_spanned(path, "Duplicate field"));
                }
            } else {
                return Err(Error::new_spanned(path, "Expected ident"));
            }
        }

        Ok(Self(map))
    }

    pub fn extract<T>(&mut self, name: &str) -> Result<T, Error>
    where
        T: Extract,
    {
        T::extract(name, &mut self.0)
    }
}
