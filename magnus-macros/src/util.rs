use syn::{spanned::Spanned, Attribute, Error};

pub fn get_magnus_attribute(attrs: &[Attribute]) -> Result<Option<&Attribute>, Error> {
    let attrs = attrs
        .iter()
        .filter(|attr| attr.path().is_ident("magnus"))
        .collect::<Vec<_>>();
    if attrs.is_empty() {
        return Ok(None);
    } else if attrs.len() > 1 {
        return Err(attrs
            .into_iter()
            .map(|a| Error::new(a.span(), "duplicate attribute"))
            .reduce(|mut a, b| {
                a.combine(b);
                a
            })
            .unwrap());
    }
    Ok(Some(attrs[0]))
}
