use std::{
    ffi::{CStr, c_void},
    ptr,
};

use rb_sys::{VALUE, rb_data_type_struct__bindgen_ty_1, rb_data_type_t, size_t};

unsafe extern "C" fn data_func(_: *mut c_void) {
    ()
}

unsafe extern "C" fn size(_: *const c_void) -> size_t {
    0
}

// We zero-initialise rb_data_type_t (e.g.
// `let mut data_type: rb_data_type_t = unsafe { mem::zeroed() };`) and then
// fill the fields to avoid referencing the bindgen generated name of the
// anonymous `function` struct and avoid compilation errors if rb_data_type_t
// changes shape. The Ruby API and usage examples do seem like it is
// deliberately designed to be used like this.
// However, while avoiding compilation errors for users is good, it'd still be
// nice to know if/when rb_data_type_t changes shape so we can make sure it's
// still fine to zero-initialise. This test acts as a canary for that purpose.

#[test]
fn it_compiles() {
    let flags: VALUE = 0;

    static NAME: &CStr = c"example";
    rb_data_type_t {
        wrap_struct_name: NAME.as_ptr(),
        function: rb_data_type_struct__bindgen_ty_1 {
            dmark: Some(data_func),
            dfree: Some(data_func),
            dsize: Some(size),
            dcompact: Some(data_func),
            #[cfg(ruby_lt_4_1)]
            reserved: [ptr::null_mut(); 1],
            #[cfg(ruby_gte_4_1)]
            reserved: [ptr::null_mut(); 7],
            #[cfg(ruby_gte_4_1)]
            handle_weak_references: None,
        },
        parent: ptr::null(),
        data: ptr::null_mut(),
        flags,
    };
    ()
}
