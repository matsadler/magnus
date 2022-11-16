use std::collections::HashMap;

use proc_macro2::Span;
use syn::{AttributeArgs, Error, Lit, Meta, MetaNameValue, NestedMeta, Path};

pub struct Value {
    path: Path,
    value: Option<Lit>,
}

pub trait Extract: Sized {
    fn extract(name: &str, map: &mut HashMap<String, Value>) -> Result<Self, Error>;
}

impl Extract for String {
    fn extract(name: &str, map: &mut HashMap<String, Value>) -> Result<Self, Error> {
        match map.remove(name) {
            Some(Value {
                value: Some(Lit::Str(lit_str)),
                ..
            }) => Ok(lit_str.value()),
            Some(Value {
                value: Some(lit), ..
            }) => Err(Error::new_spanned(lit, "Expected string")),
            Some(Value { path, .. }) => Err(Error::new_spanned(path, "Expected string")),
            None => Err(Error::new(
                Span::call_site(),
                format!("Missing field `{}`", name),
            )),
        }
    }
}

impl Extract for Option<String> {
    fn extract(name: &str, map: &mut HashMap<String, Value>) -> Result<Self, Error> {
        match map.remove(name) {
            Some(Value {
                value: Some(Lit::Str(lit_str)),
                ..
            }) => Ok(Some(lit_str.value())),
            Some(Value {
                value: Some(lit), ..
            }) => Err(Error::new_spanned(lit, "Expected string")),
            Some(Value { path, .. }) => Err(Error::new_spanned(path, "Expected string")),
            None => Ok(None),
        }
    }
}

impl Extract for Option<()> {
    fn extract(name: &str, map: &mut HashMap<String, Value>) -> Result<Self, Error> {
        match map.remove(name) {
            Some(Value {
                value: Some(lit), ..
            }) => Err(Error::new_spanned(lit, "Unexpected value")),
            Some(Value { value: None, .. }) => Ok(Some(())),
            None => Ok(None),
        }
    }
}

pub struct Args(HashMap<String, Value>);

impl Args {
    pub fn new(args: AttributeArgs, known: &[&str]) -> Result<Self, Error> {
        Self::new_with_aliases(args, known, &HashMap::new())
    }

    pub fn new_with_aliases(args: AttributeArgs, known: &[&str], aliases: &HashMap<&str, &str>) -> Result<Self, Error> {
        let mut map = HashMap::new();

        for nested_meta in args {
            let meta = match nested_meta {
                NestedMeta::Meta(v) => v,
                NestedMeta::Lit(_) => {
                    return Err(Error::new_spanned(nested_meta, "Unexpected literal"))
                }
            };

            let (path, value) = match meta {
                Meta::Path(v) => (v, None),
                Meta::List(_) => return Err(Error::new_spanned(meta, "Unexpected meta list")),
                Meta::NameValue(MetaNameValue { path, lit, .. }) => (path, Some(lit)),
            };

            if let Some(ident) = path.get_ident() {
                let s = ident.to_string();
                let s = aliases.get(&s.as_str()).map(|&s| s.to_owned()).unwrap_or(s);
                if !known.contains(&s.as_str()) {
                    return Err(Error::new_spanned(ident, "Unknown field"));
                }
                let val = Value {
                    path: path.clone(),
                    value,
                };
                if map.insert(s, val).is_some() {
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
