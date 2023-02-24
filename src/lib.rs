//! Magnus is a library for writing Ruby extentions in Rust, or running Ruby
//! code from Rust.
//!
//! # Overview
//!
//! All Ruby objects are represented by [`Value`]. To make it easier to work
//! with values that are instances of specific classes a number of wrapper
//! types are available. These wrappers and [`Value`] all implement the
//! [`ReprValue`] trait, so share many methods.
//!
//! | Ruby Class | Magnus Type |
//! |------------|-------------|
//! | `String`   | [`RString`] |
//! | `Integer`  | [`Integer`] |
//! | `Float`    | [`Float`]   |
//! | `Array`    | [`RArray`]  |
//! | `Hash`     | [`RHash`]   |
//! | `Symbol`   | [`Symbol`]  |
//! | `Class`    | [`RClass`]  |
//! | `Module`   | [`RModule`] |
//!
//! When writing Rust code to be called from Ruby the [`init`] attribute can
//! be used to mark your init function that Ruby will call when your library
//! is `require`d.
//!
//! When embedding Ruby in a Rust program, see [`embed::init`] for initialising
//! the Ruby VM.
//!
//! The [`method`](`macro@method`) macro can be used to wrap a Rust function
//! with automatic type conversion and error handing so it can be exposed to
//! Ruby. The [`TryConvert`] trait handles conversions from Ruby to Rust, and
//! anything implementing [`IntoValue`] can be returned to Ruby. See the
//! [`Module`] and [`Object`] traits for defining methods.
//!
//! [`Value::funcall`] can be used to call Ruby methods from Rust.
//!
//! See the [`wrap`] attribute macro for wrapping Rust types as Ruby objects.
//!
//! ## Safety
//!
//! When using Magnus, in Rust code, Ruby objects must be kept on the stack. If
//! objects are moved to the heap the Ruby GC can not reach them, and they may
//! be garbage collected. This could lead to memory safety issues.
//!
//! It is not possible to enforce this rule in Rust's type system or via the
//! borrow checker, users of Magnus must maintain this rule manually.
//!
//! An example of something that breaks this rule would be storing a Ruby
//! object in a Rust heap allocated data structure, such as `Vec`, `HashMap`,
//! or `Box`. This must be avoided at all costs.
//!
//! While it would be possible to mark any functions that could expose this
//! unsafty as `unsafe`, that would mean that almost every interaction with
//! Ruby would be `unsafe`. This would leave no way to differentiate the
//! *really* unsafe functions that need much more care to use.
//!
//! # Examples
//!
//! ```
//! use magnus::{class, define_module, function, method, prelude::*, Error};
//!
//! #[magnus::wrap(class = "Euclid::Point", free_immediately, size)]
//! struct Point {
//!     x: isize,
//!     y: isize,
//! }
//!
//! impl Point {
//!     fn new(x: isize, y: isize) -> Self {
//!         Self { x, y }
//!     }
//!
//!     fn x(&self) -> isize {
//!         self.x
//!     }
//!
//!     fn y(&self) -> isize {
//!         self.y
//!     }
//! }
//!
//! fn distance(a: &Point, b: &Point) -> f64 {
//!     (((b.x - a.x).pow(2) + (b.y - a.y).pow(2)) as f64).sqrt()
//! }
//!
//! #[magnus::init]
//! fn init() -> Result<(), Error> {
//!     let module = define_module("Euclid")?;
//!     let class = module.define_class("Point", class::object())?;
//!     class.define_singleton_method("new", function!(Point::new, 2))?;
//!     class.define_method("x", method!(Point::x, 0))?;
//!     class.define_method("y", method!(Point::y, 0))?;
//!     module.define_module_function("distance", function!(distance, 2))?;
//!     Ok(())
//! }
//! ```
//!
//! # Crates that work with Magnus
//!
//! * [`rb-sys`](https://docs.rs/rb-sys) - low level bindings to Ruby.
//! * [`serde_magnus`](https://docs.rs/serde_magnus) - Serde integration.
//!
//! # C Function Index
//! <details>
//! <summary>Click to show</summary>
//!
//! This lists all the Ruby C API functions currently implemented, and how they
//! map to Rust functions and methods in Magnus.
//!
// Currently unimplemented listed here, but not included in doc comments. The
// plan is to start listing what's planned to implement, what can't/won't be
// implemented, alternatives, etc.
//!
//! ## A-N
//!
// * `Check_Type`:
//! * `Data_Get_Struct`: See [`wrap`] and [`TypedData`].
//! * `Data_Make_Struct`: See [`wrap`] and [`TypedData`].
//! * `Data_Wrap_Struct`: See [`wrap`] and [`TypedData`].
// * `ExportStringValue`:
//!
// ## `onig`
//!
// * `onigenc_ascii_only_case_map`:
// * `onigenc_get_default_encoding`:
// * `onigenc_get_left_adjust_char_head`:
// * `onigenc_get_prev_char_head`:
// * `onigenc_get_right_adjust_char_head`:
// * `onigenc_get_right_adjust_char_head_with_prev`:
// * `onigenc_init`:
// * `onigenc_mbclen_approximate`:
// * `onigenc_set_default_encoding`:
// * `onigenc_step_back`:
// * `onigenc_strlen`:
// * `onigenc_strlen_null`:
// * `onigenc_str_bytelen_null`:
// * `onig_capture_tree_traverse`:
// * `onig_copyright`:
// * `onig_copy_encoding`:
// * `onig_copy_syntax`:
// * `onig_end`:
// * `onig_error_code_to_str`:
// * `onig_foreach_name`:
// * `onig_free`:
// * `onig_free_body`:
// * `onig_get_case_fold_flag`:
// * `onig_get_default_case_fold_flag`:
// * `onig_get_encoding`:
// * `onig_get_match_stack_limit_size`:
// * `onig_get_options`:
// * `onig_get_parse_depth_limit`:
// * `onig_get_syntax`:
// * `onig_get_syntax_behavior`:
// * `onig_get_syntax_op`:
// * `onig_get_syntax_op2`:
// * `onig_get_syntax_options`:
// * `onig_init`:
// * `onig_initialize`:
// * `onig_match`:
// * `onig_name_to_backref_number`:
// * `onig_name_to_group_numbers`:
// * `onig_new`:
// * `onig_new_deluxe`:
// * `onig_new_without_alloc`:
// * `onig_noname_group_capture_is_active`:
// * `onig_null_warn`:
// * `onig_number_of_captures`:
// * `onig_number_of_capture_histories`:
// * `onig_number_of_names`:
// * `onig_region_clear`:
// * `onig_region_copy`:
// * `onig_region_free`:
// * `onig_region_init`:
// * `onig_region_new`:
// * `onig_region_resize`:
// * `onig_region_set`:
// * `onig_reg_init`:
// * `onig_scan`:
// * `onig_search`:
// * `onig_search_gpos`:
// * `onig_set_default_case_fold_flag`:
// * `onig_set_default_syntax`:
// * `onig_set_match_stack_limit_size`:
// * `onig_set_meta_char`:
// * `onig_set_parse_depth_limit`:
// * `onig_set_syntax_behavior`:
// * `onig_set_syntax_op`:
// * `onig_set_syntax_op2`:
// * `onig_set_syntax_options`:
// * `onig_set_verb_warn_func`:
// * `onig_set_warn_func`:
// * `onig_version`:
//
//! ## `RARRAY`
//
//! * `RARRAY`: Similar to [`RArray::from_value`].
//! * `RARRAY_ASET`: Similar to [`RArray::store`].
//! * `RARRAY_CONST_PTR`: Similar to [`RArray::as_slice`].
// * `RARRAY_CONST_PTR_TRANSIENT`:
//! * `RARRAY_EMBED_LEN`: See [`RArray::len`].
//! * `RARRAY_LEN`: [`RArray::len`].
//! * `RARRAY_LENINT`: [`RArray::len`].
//! * `RARRAY_PTR`: Similar to [`RArray::as_slice`].
// * `RARRAY_PTR_USE`:
// * `RARRAY_PTR_USE_END`:
// * `RARRAY_PTR_USE_END_TRANSIENT`:
// * `RARRAY_PTR_USE_START`:
// * `RARRAY_PTR_USE_START_TRANSIENT`:
// * `RARRAY_PTR_USE_TRANSIENT`:
// * `RARRAY_TRANSIENT_P`:
//!
//! ## RB
//!
// * `RBASIC`:
// * `RBASIC_CLASS`:
//! * `RBIGNUM_NEGATIVE_P`: See [`RBignum::is_negative`].
//! * `RBIGNUM_POSITIVE_P`: See [`RBignum::is_positive`].
// * `RBIGNUM_SIGN`:
//!
//! ## `rb_a`-`rb_arx`
//!
// * `rb_absint_numwords`:
// * `rb_absint_singlebit_p`:
// * `rb_absint_size`:
// * `rb_add_event_hook`:
// * `rb_add_event_hook2`:
//! * `rb_alias`: [`Module::define_alias`].
// * `rb_alias_variable`:
// * `RB_ALLOC`:
// * `RB_ALLOCV`:
// * `RB_ALLOCV_END`:
// * `RB_ALLOCV_N`:
// * `RB_ALLOC_N`:
// * `rb_alloc_tmp_buffer`:
// * `rb_alloc_tmp_buffer2`:
// * `rb_alloc_tmp_buffer_with_count`:
//! * `rb_any_to_s`: [`std::fmt::Display`].
// * `rb_apply`:
// * `rb_argv`:
// * `rb_arithmetic_sequence_beg_len_step`:
// * `rb_arithmetic_sequence_extract`:
// * `rb_Array`:
// * `rb_array_len`:
//!
//! ## `rb_ary`
//!
// * `rb_ary_aref`:
//! * `rb_ary_assoc`: [`RArray::assoc`].
//! * `rb_ary_cat`: [`RArray::cat`].
//! * `rb_ary_clear`: [`RArray::clear`].
//! * `rb_ary_cmp`: [`RArray::cmp`].
//! * `rb_ary_concat`: [`RArray::concat`].
//! * `rb_ary_delete`: [`RArray::delete`].
//! * `rb_ary_delete_at`: [`RArray::delete_at`].
// * `rb_ary_detransient`:
//! * `rb_ary_dup`: Similar to [`RArray::dup`].
//! * `rb_ary_each`: See [`RArray::each`].
//! * `rb_ary_entry`: [`RArray::entry`].
// * `rb_ary_free`:
//! * `rb_ary_freeze`: See [`Value::freeze`].
//! * `rb_ary_includes`: [`RArray::includes`].
// * `rb_ary_join`: [`RArray::join`].
// * `rb_ary_modify`:
//! * `rb_ary_new`: [`RArray::new`].
//! * `rb_ary_new_capa`: [`RArray::with_capacity`].
//! * `rb_ary_new_from_args`: Not implemented, see [`RArray::from_slice`].
//! * `rb_ary_new_from_values`: [`RArray::from_slice`].
//! * `rb_ary_plus`: [`RArray::plus`].
//! * `rb_ary_pop`: [`RArray::pop`].
// * `rb_ary_ptr_use_end`:
// * `rb_ary_ptr_use_start`:
//! * `rb_ary_push`: [`RArray::push`].
//! * `rb_ary_rassoc`: [`RArray::rassoc`].
//! * `rb_ary_replace`: [`RArray::replace`].
//! * `rb_ary_resize`: [`RArray::resize`].
// * `rb_ary_resurrect`:
//! * `rb_ary_reverse`: [`RArray::reverse`].
//! * `rb_ary_rotate`: [`RArray::rotate`].
//! * `rb_ary_shared_with_p`: [`RArray::is_shared`].
//! * `rb_ary_shift`: [`RArray::shift`].
//! * `rb_ary_sort`: Not implemented, see [`RArray::sort`].
//! * `rb_ary_sort_bang`: [`RArray::sort`].
//! * `rb_ary_store`: [`RArray::store`].
//! * `rb_ary_subseq`: [`RArray::subseq`].
// * `rb_ary_tmp_new`:
//! * `rb_ary_to_ary`: [`RArray::to_ary`].
//! * `rb_ary_to_s`: Not implemented directly, see [`Value::to_r_string`].
//! * `rb_ary_unshift`: [`RArray::unshift`].
//!
//! ## `rb_as`-`rb_az`
//!
//! * `rb_ascii8bit_encindex`: [`encoding::Index::ascii8bit`].
//! * `rb_ascii8bit_encoding`:
//!   [`RbEncoding::ascii8bit`](encoding::RbEncoding::ascii8bit).
// * `rb_assert_failure`:
// * `rb_assoc_new`:
//! * `rb_attr`: [`Module::define_attr`].
// * `rb_attr_get`:
// * `rb_autoload`:
// * `rb_autoload_load`:
// * `rb_autoload_p`:
//!
//! ## `rb_b`
//!
//! * `rb_backref_get`: [`backref_get`].
// * `rb_backref_set`:
// * `rb_backtrace`:
// * `rb_big2dbl`:
// * `rb_big2int`:
// * `rb_big2ll`:
// * `rb_big2long`:
// * `rb_big2str`:
// * `rb_big2uint`:
// * `rb_big2ull`:
// * `rb_big2ulong`:
// * `rb_bigzero_p`:
// * `rb_big_2comp`:
// * `rb_big_and`:
// * `rb_big_clone`:
// * `rb_big_cmp`:
// * `rb_big_div`:
// * `rb_big_divmod`:
// * `rb_big_eq`:
// * `rb_big_eql`:
// * `rb_big_idiv`:
// * `rb_big_lshift`:
// * `rb_big_minus`:
// * `rb_big_modulo`:
// * `rb_big_mul`:
// * `rb_big_new`:
// * `rb_big_norm`:
// * `rb_big_or`:
// * `rb_big_pack`:
// * `rb_big_plus`:
// * `rb_big_pow`:
// * `rb_big_resize`:
// * `rb_big_rshift`:
// * `rb_big_sign`:
// * `rb_big_unpack`:
// * `rb_big_xor`:
//! * `rb_binding_new`: [`Binding::new`]. Unimplemented >= Ruby 3.2.
//! * `rb_block_call`: [`Value::block_call`].
// * `rb_block_call_kw`:
//! * `rb_block_given_p`: [`block::block_given`].
// * `rb_block_lambda`:
//! * `rb_block_proc`: [`block::block_proc`].
//! * `rb_bug`: [`error::bug`].
// * `rb_bug_errno`:
// * `RB_BUILTIN_TYPE`:
//!
//! ## `rb_c`
//!
//! * `rb_call_super`: [`call_super`].
// * `rb_call_super_kw`:
// * `rb_catch`:
// * `rb_catch_obj`:
// * `rb_category_compile_warn`:
// * `rb_category_warn`:
// * `rb_category_warning`:
// * `rb_char_to_option_kcode`:
//! * `rb_check_arity`: [`scan_args::check_arity`].
//! * `rb_check_array_type`:  See [`TryConvert`] and [`Value::try_convert`].
// * `rb_check_convert_type`:
// * `rb_check_copyable`:
// * `rb_check_frozen`:
// * `rb_check_frozen_inline`:
//! * `rb_check_funcall`: [`Value::check_funcall`].
// * `rb_check_funcall_kw`:
//! * `rb_check_hash_type`: See [`TryConvert`] and [`Value::try_convert`].
//! * `rb_check_id`: Similar to [`Id::check`](value::Id::check).
//! * `rb_check_id_cstr`: [`Id::check`](value::Id::check).
// * `rb_check_inheritable`:
// * `rb_check_safe_str`:
// * `rb_check_string_type`:
//! * `rb_check_symbol`: Similar to [`StaticSymbol::check`].
//! * `rb_check_symbol_cstr`: [`StaticSymbol::check`].
// * `rb_check_to_float`:
// * `rb_check_to_int`:
// * `rb_check_to_integer`:
// * `rb_check_type`:
//! * `rb_check_typeddata`: See [`TryConvert`] and [`Value::try_convert`].
// * `RB_CHR2FIX`:
//! * `rb_class2name`: [`RClass::name`].
// * `rb_class_descendants`:
// * `rb_class_get_superclass`:
// * `rb_class_inherited_p`: [`Module::is_inherited`].
// * `rb_class_instance_methods`:
//! * `rb_class_name`: Simmilar to [`Value::classname`].
//! * `rb_class_new`: [`RClass::new`].
//! * `rb_class_new_instance`: [`RClass::new_instance`].
// * `rb_class_new_instance_kw`:
// * `rb_class_new_instance_pass_kw`:
// * `rb_class_of`:
// * `rb_class_path`:
// * `rb_class_path_cached`:
// * `rb_class_private_instance_methods`:
// * `rb_class_protected_instance_methods`:
// * `rb_class_public_instance_methods`:
// * `rb_class_real`:
// * `rb_class_subclasses`:
//! * `rb_class_superclass`: [`RClass::superclass`].
// * `rb_clear_constant_cache`:
// * `rb_clear_trace_func`:
// * `rb_cloexec_dup`:
// * `rb_cloexec_dup2`:
// * `rb_cloexec_fcntl_dupfd`:
// * `rb_cloexec_open`:
// * `rb_cloexec_pipe`:
// * `rb_close_before_exec`:
// * `rb_cmperr`:
// * `rb_cmpint`:
// * `rb_compile_error`:
// * `rb_compile_error_append`:
// * `rb_compile_error_with_enc`:
// * `rb_compile_warn`:
// * `rb_compile_warning`:
// * `rb_Complex`:
// * `rb_Complex1`:
// * `rb_Complex2`:
//! * `rb_complex_abs`: [`RComplex::abs`].
// * `rb_complex_add`:
//! * `rb_complex_arg`: [`RComplex::arg`].
//! * `rb_complex_conjugate`: [`RComplex::conjugate`].
// * `rb_complex_div`:
//! * `rb_complex_imag`: [`RComplex::imag`].
// * `rb_complex_minus`:
// * `rb_complex_mul`:
// * `rb_complex_nagate`:
//! * `rb_complex_new`: [`RComplex::new`].
// * `rb_complex_new1`:
// * `rb_complex_new2`:
//! * `rb_complex_new_polar`: [`RComplex::polar`].
// * `rb_complex_plus`:
// * `rb_complex_pow`:
// * `rb_complex_raw`:
// * `rb_complex_raw1`:
// * `rb_complex_raw2`:
//! * `rb_complex_real`: [`RComplex::real`].
// * `rb_complex_sub`:
// * `rb_complex_uminus`:
// * `rb_const_defined`:
// * `rb_const_defined_at`:
// * `rb_const_defined_from`:
//! * `rb_const_get`: [`Module::const_get`].
// * `rb_const_get_at`:
// * `rb_const_get_from`:
// * `rb_const_list`:
// * `rb_const_remove`:
//! * `rb_const_set`: [`Module::const_set`].
// * `rb_convert_type`:
// * `rb_copy_generic_ivar`:
// * `rb_cstr2inum`:
// * `rb_cstr_to_dbl`:
// * `rb_cstr_to_inum`:
//! * `rb_current_receiver`: [`current_receiver`].
// * `rb_cvar_defined`:
// * `rb_cvar_find`:
// * `rb_cvar_get`:
// * `rb_cvar_set`:
// * `rb_cv_get`:
// * `rb_cv_set`:
//!
//! ## `rb_d`
//!
//! * `rb_data_object_make`: See [`wrap`] and [`TypedData`].
//! * `rb_data_object_wrap`: See [`wrap`] and [`TypedData`].
//! * `rb_data_object_zalloc`: See [`wrap`] and [`TypedData`].
//! * `rb_data_typed_object_make`: See [`wrap`] and [`TypedData`].
//! * `rb_data_typed_object_wrap`: See [`wrap`] and [`TypedData`].
//! * `rb_data_typed_object_zalloc`: See [`wrap`] and [`TypedData`].
// * `rb_dbl2big`:
// * `rb_dbl_cmp`:
// * `rb_dbl_complex_new`:
// * `rb_debug_inspector_backtrace_locations`:
// * `rb_debug_inspector_frame_binding_get`:
// * `rb_debug_inspector_frame_class_get`:
// * `rb_debug_inspector_frame_iseq_get`:
// * `rb_debug_inspector_frame_self_get`:
// * `rb_debug_inspector_open`:
// * `rb_debug_rstring_null_ptr`:
//! * `rb_default_external_encoding`:
//!   [`RbEncoding::default_external`](encoding::RbEncoding::default_external).
//! * `rb_default_internal_encoding`:
//!   [`RbEncoding::default_internal`](encoding::RbEncoding::default_internal).
//! * `rb_define_alias`: [`Module::define_alias`].
// * `rb_define_alloc_func`:
//! * `rb_define_attr`: See [`Module::define_attr`].
//! * `rb_define_class`: [`define_class`].
//! * `rb_define_class_id`: Simmilar to [`define_class`].
//! * `rb_define_class_id_under`: [`Module::define_class`].
//! * `rb_define_class_under`: See [`Module::define_class`].
// * `rb_define_class_variable`:
// * `rb_define_const`:
// * `rb_define_dummy_encoding`:
// * `rb_define_finalizer`:
// * `rb_define_global_const`:
//! * `rb_define_global_function`: [`define_global_function`].
// * `rb_define_hooked_variable`:
//! * `rb_define_method`: See [`Module::define_method`].
//! * `rb_define_method_id`: [`Module::define_method`].
//! * `rb_define_module`: [`define_module`].
//! * `rb_define_module_function`: [`RModule::define_module_function`].
//! * `rb_define_module_id`: See [`define_module`].
//! * `rb_define_module_id_under`: [`Module::define_module`].
//! * `rb_define_module_under`: See [`Module::define_module`].
//! * `rb_define_private_method`: [`Module::define_private_method`].
//! * `rb_define_protected_method`: [`Module::define_protected_method`].
// * `rb_define_readonly_variable`:
//! * `rb_define_singleton_method`: [`Object::define_singleton_method`].
//! * `rb_define_variable`: [`define_variable`].
// * `rb_define_virtual_variable`:
// * `rb_deprecate_constant`:
// * `rb_detach_process`:
// * `rb_dir_getwd`:
// * `rb_disable_super`:
// * `rb_during_gc`:
// * `RB_DYNAMIC_SYM_P`:
//!
//! ## `rb_e`-`rb_enb`
//!
// * `rb_each`:
// * `rb_econv_append`:
// * `rb_econv_asciicompat_encoding`:
// * `rb_econv_binmode`:
// * `rb_econv_check_error`:
// * `rb_econv_close`:
// * `rb_econv_convert`:
// * `rb_econv_decorate_at_first`:
// * `rb_econv_decorate_at_last`:
// * `rb_econv_encoding_to_insert_output`:
// * `rb_econv_has_convpath_p`:
// * `rb_econv_insert_output`:
// * `rb_econv_make_exception`:
// * `rb_econv_open`:
// * `rb_econv_open_exc`:
// * `rb_econv_open_opts`:
// * `rb_econv_prepare_options`:
// * `rb_econv_prepare_opts`:
// * `rb_econv_putback`:
// * `rb_econv_putbackable`:
// * `rb_econv_set_replacement`:
// * `rb_econv_str_append`:
// * `rb_econv_str_convert`:
// * `rb_econv_substr_append`:
// * `rb_econv_substr_convert`:
// * `rb_enable_super`:
//!
//! ## `rb_enc`
//!
// * `RB_ENCODING_CODERANGE_SET`:
// * `RB_ENCODING_GET`:
// * `RB_ENCODING_GET_INLINED`:
// * `RB_ENCODING_IS_ASCII8BIT`:
// * `RB_ENCODING_SET`:
// * `RB_ENCODING_SET_INLINED`:
// * `rb_enc_alias`:
//! * `rb_enc_ascget`: [`RbEncoding::ascget`](encoding::RbEncoding::ascget).
// * `rb_enc_asciicompat`:
//! * `rb_enc_associate`:
//!   See [`EncodingCapable::enc_associate`](encoding::EncodingCapable::enc_associate).
//! * `rb_enc_associate_index`:
//!   [`EncodingCapable::enc_associate`](encoding::EncodingCapable::enc_associate).
// * `rb_enc_capable`:
//! * `rb_enc_check`: [`encoding::check`].
//! * `rb_enc_codelen`: [`RbEncoding::codelen`](encoding::RbEncoding::codelen).
//! * `rb_enc_codepoint_len`:
//!   [`RbEncoding::codepoint_len`](encoding::RbEncoding::codepoint_len).
//! * `RB_ENC_CODERANGE`: [`RString::enc_coderange`].
// * `RB_ENC_CODERANGE_AND`:
// * `RB_ENC_CODERANGE_ASCIIONLY`:
// * `RB_ENC_CODERANGE_CLEAN_P`:
//! * `RB_ENC_CODERANGE_CLEAR`: [`RString::enc_coderange_clear`].
//! * `RB_ENC_CODERANGE_SET`: [`RString::enc_coderange_set`].
// * `rb_enc_code_to_mbclen`:
//! * `rb_enc_compatible`: [`encoding::compatible`].
//! * `rb_enc_copy`: [`encoding::copy`].
//! * `rb_enc_default_external`:
//!   [`Encoding::default_external`](encoding::Encoding::default_external).
// * `rb_enc_default_internal`:
//!   [`Encoding::default_internal`](encoding::Encoding::default_internal).
// * `rb_enc_dummy_p`:
//! * `rb_enc_fast_mbclen`:
//!   [`RbEncoding::fast_mbclen`](encoding::RbEncoding::fast_mbclen).
//! * `rb_enc_find`: [`RbEncoding::find`](encoding::RbEncoding::find).
//! * `rb_enc_find_index`: [`encoding::Index::find`].
//! * `rb_enc_from_encoding`: [`std::convert::From`].
//! * `rb_enc_from_index`: [`std::convert::From`].
//! * `rb_enc_get`: Use [`EncodingCapable::enc_get`](encoding::EncodingCapable::enc_get)
//!   plus [`std::convert::From`].
//! * `rb_enc_get_index`:
//!   [`EncodingCapable::enc_get`](encoding::EncodingCapable::enc_get).
// * `rb_enc_interned_str`:
// * `rb_enc_interned_str_cstr`:
// * `rb_enc_isalnum`:
// * `rb_enc_isalpha`:
// * `rb_enc_isascii`:
// * `rb_enc_isctype`:
// * `rb_enc_isdigit`:
// * `rb_enc_islower`:
// * `rb_enc_isprint`:
// * `rb_enc_ispunct`:
// * `rb_enc_isspace`:
// * `rb_enc_isupper`:
// * `rb_enc_is_newline`:
// * `rb_enc_left_char_head`:
//! * `rb_enc_mbclen`: [`RbEncoding::mbclen`](encoding::RbEncoding::mbclen).
// * `rb_enc_mbcput`:
// * `rb_enc_mbc_to_codepoint`:
// * `rb_enc_mbmaxlen`:
// * `rb_enc_mbminlen`:
// * `rb_enc_name`:
// * `rb_enc_nth`:
// * `rb_enc_path_end`:
// * `rb_enc_path_last_separator`:
// * `rb_enc_path_next`:
// * `rb_enc_path_skip_prefix`:
//! * `rb_enc_precise_mbclen`:
//!   [`RbEncoding::precise_mbclen`](encoding::RbEncoding::precise_mbclen).
// * `rb_enc_prev_char`:
// * `rb_enc_raise`:
//! * `rb_enc_reg_new`: [`RRegexp::new`].
// * `rb_enc_replicate`:
// * `rb_enc_right_char_head`:
// * `rb_enc_set_default_external`:
// * `rb_enc_set_default_internal`:
//! * `rb_enc_set_index`:
//!   [`EncodingCapable::enc_set`](encoding::EncodingCapable::enc_set).
// * `rb_enc_sprintf`:
// * `rb_enc_step_back`:
// * `rb_enc_strlen`:
// * `rb_enc_str_asciicompat_p`:
// * `rb_enc_str_asciionly_p`:
// * `rb_enc_str_buf_cat`:
//! * `rb_enc_str_coderange`: [`RString::enc_coderange_scan`].
//! * `rb_enc_str_new`: [`RString::enc_new`].
// * `rb_enc_str_new_cstr`:
// * `rb_enc_str_new_lit`:
// * `rb_enc_str_new_literal`:
// * `rb_enc_str_new_static`:
// * `rb_enc_symname2_p`:
// * `rb_enc_symname_p`:
// * `rb_enc_tolower`:
// * `rb_enc_toupper`:
//! * `rb_enc_to_index`: [`std::convert::From`].
//! * `rb_enc_uint_chr`: [`RbEncoding::chr`](encoding::RbEncoding::chr).
// * `rb_enc_unicode_p`:
// * `rb_enc_vsprintf`:
//!
//! ## `rb_en`-`rb_ez`
//!
// * `rb_ensure`:
//! * `rb_enumeratorize`: See [`Value::enumeratorize`].
//! * `rb_enumeratorize_with_size`: Simmilar to [`Value::enumeratorize`].
// * `rb_enumeratorize_with_size_kw`:
// * `rb_enum_values_pack`:
// * `rb_env_clear`:
// * `rb_eof_error`:
//! * `rb_eql`: [`Value::eql`].
//! * `rb_equal`: [`Value::equal`].
// * `rb_errinfo`:
//! * `rb_error_arity`: [`scan_args::check_arity`].
// * `rb_error_frozen`:
// * `rb_error_frozen_object`:
// * `rb_eval_cmd_kw`:
//! * `rb_eval_string`: See [`eval()`] or [`eval!`].
//! * `rb_eval_string_protect`: [`eval()`] or [`eval!`].
// * `rb_eval_string_wrap`:
// * `rb_exc_fatal`:
// * `rb_exc_new`:
// * `rb_exc_new_cstr`:
// * `rb_exc_new_str`:
//! * `rb_exc_raise`: Return [`Error`].
// * `rb_exec_end_proc`:
// * `rb_exec_recursive`:
// * `rb_exec_recursive_outer`:
// * `rb_exec_recursive_paired`:
// * `rb_exec_recursive_paired_outer`:
// * `rb_exit`:
//! * `rb_extend_object`: [`Object::extend_object`].
// * `rb_external_str_new`:
// * `rb_external_str_new_cstr`:
// * `rb_external_str_new_with_enc`:
// * `rb_extract_keywords`:
// * `RB_EXT_RACTOR_SAFE`:
// * `rb_ext_ractor_safe`:
//!
//! ## `rb_f`
//!
// * `rb_fatal`:
// * `rb_fdopen`:
// * `rb_fd_clr`:
// * `rb_fd_copy`:
// * `rb_fd_dup`:
// * `rb_fd_fix_cloexec`:
// * `rb_fd_init`:
// * `rb_fd_isset`:
// * `rb_fd_max`:
// * `rb_fd_ptr`:
// * `rb_fd_resize`:
// * `rb_fd_select`:
// * `rb_fd_set`:
// * `rb_fd_term`:
// * `rb_fd_zero`:
// * `rb_feature_provided`:
// * `rb_fiber_alive_p`:
// * `rb_fiber_current`:
// * `rb_fiber_new`:
// * `rb_fiber_raise`:
// * `rb_fiber_resume`:
// * `rb_fiber_resume_kw`:
// * `rb_fiber_scheduler_address_resolve`:
// * `rb_fiber_scheduler_block`:
// * `rb_fiber_scheduler_close`:
// * `rb_fiber_scheduler_current`:
// * `rb_fiber_scheduler_current_for_thread`:
// * `rb_fiber_scheduler_get`:
// * `rb_fiber_scheduler_io_close`:
// * `rb_fiber_scheduler_io_pread`:
// * `rb_fiber_scheduler_io_pwrite`:
// * `rb_fiber_scheduler_io_read`:
// * `rb_fiber_scheduler_io_read_memory`:
// * `rb_fiber_scheduler_io_result`:
// * `rb_fiber_scheduler_io_result_apply`:
// * `rb_fiber_scheduler_io_wait`:
// * `rb_fiber_scheduler_io_wait_readable`:
// * `rb_fiber_scheduler_io_wait_writable`:
// * `rb_fiber_scheduler_io_write`:
// * `rb_fiber_scheduler_io_write_memory`:
// * `rb_fiber_scheduler_kernel_sleep`:
// * `rb_fiber_scheduler_kernel_sleepv`:
// * `rb_fiber_scheduler_make_timeout`:
// * `rb_fiber_scheduler_process_wait`:
// * `rb_fiber_scheduler_set`:
// * `rb_fiber_scheduler_unblock`:
// * `rb_fiber_transfer`:
// * `rb_fiber_transfer_kw`:
// * `rb_fiber_yield`:
// * `rb_fiber_yield_kw`:
//! * `rb_filesystem_encindex`: [`encoding::Index::filesystem`].
//! * `rb_filesystem_encoding`:
//!   [`RbEncoding::filesystem`](encoding::RbEncoding::filesystem).
// * `rb_filesystem_str_new`:
// * `rb_filesystem_str_new_cstr`:
// * `rb_file_absolute_path`:
// * `rb_file_directory_p`:
// * `rb_file_dirname`:
// * `rb_file_expand_path`:
// * `rb_file_open`:
// * `rb_file_open_str`:
// * `rb_file_size`:
// * `rb_file_s_absolute_path`:
// * `rb_file_s_expand_path`:
//! * `rb_find_encoding`: [`std::convert::From`].
// * `rb_find_file`:
// * `rb_find_file_ext`:
// * `RB_FIX2INT`:
// * `rb_fix2int`:
// * `RB_FIX2LONG`:
// * `rb_fix2long`:
// * `RB_FIX2SHORT`:
// * `rb_fix2short`:
// * `rb_fix2str`:
// * `RB_FIX2UINT`:
// * `rb_fix2uint`:
// * `RB_FIX2ULONG`:
// * `rb_fix2ulong`:
// * `rb_fix2ushort`:
// * `RB_FIXABLE`:
// * `RB_FIXNUM_P`:
// * `rb_fix_new`:
// * `rb_Float`:
//! * `rb_float_new`: [`RFloat::from_f64`] or [`Float::from_f64`].
//! * `rb_float_new_in_heap`: See [`Float::from_f64`].
// * `RB_FLOAT_TYPE_P`:
// * `rb_float_value`: [`RFloat::to_f64`] or [`Float::to_f64`].
// * `RB_FLONUM_P`:
//! * `rb_flt_rationalize`: [`Float::rationalize`].
//! * `rb_flt_rationalize_with_prec`: [`Float::rationalize_with_prec`].
// * `RB_FL_ABLE`:
// * `RB_FL_ALL`:
// * `RB_FL_ALL_RAW`:
// * `RB_FL_ANY`:
// * `RB_FL_ANY_RAW`:
// * `RB_FL_REVERSE`:
// * `RB_FL_REVERSE_RAW`:
// * `RB_FL_SET`:
// * `RB_FL_SET_RAW`:
// * `RB_FL_TEST`:
// * `RB_FL_TEST_RAW`:
// * `RB_FL_UNSET`:
// * `RB_FL_UNSET_RAW`:
// * `rb_frame_callee`:
// * `rb_frame_method_id_and_class`:
// * `rb_frame_this_func`:
// * `rb_freeze_singleton_class`:
// * `rb_free_generic_ivar`:
// * `rb_free_tmp_buffer`:
// * `rb_frozen_class_p`:
// * `rb_frozen_error_raise`:
//! * `rb_funcall`: See [`Value::funcall`].
//! * `rb_funcallv`: [`Value::funcall`].
// * `rb_funcallv_kw`:
//! * `rb_funcallv_public`: [`Value::funcall_public`].
// * `rb_funcallv_public_kw`:
// * `rb_funcall_passing_block`:
// * `rb_funcall_passing_block_kw`:
//! * `rb_funcall_with_block`: [`Value::funcall_with_block`].
// * `rb_funcall_with_block_kw`:
// * `rb_f_abort`:
// * `rb_f_exec`:
// * `rb_f_exit`:
// * `rb_f_global_variables`:
// * `rb_f_kill`:
// * `rb_f_notimplement`:
// * `rb_f_require`:
// * `rb_f_sprintf`:
// * `rb_f_trace_var`:
// * `rb_f_untrace_var`:
//!
//! ## `rb_g`
//!
//! * `rb_gc`: [`gc::start`].
//! * `rb_gc_adjust_memory_usage`: [`gc::adjust_memory_usage`].
// * `rb_gc_call_finalizer_at_exit`:
// * `rb_gc_copy_finalizer`:
//! * `rb_gc_count`: [`gc::count`].
//! * `rb_gc_disable`: [`gc::disable`].
//! * `rb_gc_enable`: [`gc::enable`].
// * `RB_GC_GUARD`:
// * `rb_gc_latest_gc_info`:
//! * `rb_gc_location`: [`gc::location`].
//! * `rb_gc_mark`: [`gc::mark`].
//! * `rb_gc_mark_locations`: [`gc::mark_slice`].
// * `rb_gc_mark_maybe`:
//! * `rb_gc_mark_movable`: [`gc::mark_movable`].
//! * `rb_gc_register_address`: [`gc::register_address`] or
//!   [`BoxValue`](value::BoxValue).
//! * `rb_gc_register_mark_object`: [`gc::register_mark_object`].
//! * `rb_gc_start`: [`gc::start`].
//! * `rb_gc_stat`: [`gc::stat`] or [`gc::all_stats`].
//! * `rb_gc_unregister_address`: [`gc::unregister_address`].
// * `rb_gc_update_tbl_refs`:
// * `rb_gc_writebarrier`:
// * `rb_gc_writebarrier_unprotect`:
// * `rb_generic_ivar_table`:
// * `rb_genrand_int32`:
// * `rb_genrand_real`:
// * `rb_genrand_ulong_limited`:
// * `rb_gets`:
// * `rb_get_alloc_func`:
// * `rb_get_argv`:
//! * `rb_get_kwargs`: [`scan_args::get_kwargs`].
//! * `rb_get_path`: [`TryConvert`]/[`Value::try_convert`] to [`std::path::PathBuf`].
// * `rb_get_values_at`:
// * `rb_glob`:
// * `rb_global_variable`:
// * `rb_gvar_readonly_setter`:
// * `rb_gvar_val_getter`:
// * `rb_gvar_val_marker`:
// * `rb_gvar_val_setter`:
// * `rb_gv_get`:
// * `rb_gv_set`:
//!
//! # `rb_h`
//!
// * `rb_Hash`:
//! * `rb_hash`: [`Value::hash`].
//! * `rb_hash_aref`: [`RHash::aref`].
//! * `rb_hash_aset`: [`RHash::aset`].
//! * `rb_hash_bulk_insert`: [`RHash::bulk_insert`].
// * `rb_hash_bulk_insert_into_st_table`:
//! * `rb_hash_clear`: [`RHash::clear`].
//! * `rb_hash_delete`: [`RHash::delete`].
// * `rb_hash_delete_if`:
// * `rb_hash_dup`:
// * `rb_hash_end`:
//! * `rb_hash_fetch`: [`RHash::fetch`].
//! * `rb_hash_foreach`: [`RHash::foreach`].
// * `rb_hash_freeze`: See [`Value::freeze`].
// * `rb_hash_ifnone`:
// * `rb_hash_iter_lev`:
//! * `rb_hash_lookup`: [`RHash::lookup`].
//! * `rb_hash_lookup2`: [`RHash::get`].
//! * `rb_hash_new`: [`RHash::new`].
//! * `rb_hash_new_capa`: [`RHash::with_capacity`].
// * `rb_hash_set_ifnone`:
//! * `rb_hash_size`: [`RHash::size`].
//! * `rb_hash_size_num`: [`RHash::len`].
// * `rb_hash_start`:
// * `rb_hash_tbl`:
// * `rb_hash_uint`:
// * `rb_hash_uint32`:
//! * `rb_hash_update_by`: [`RHash::update`] (`update_func` arg not implemented).
//!
//! ## `rb_i`-`rb_in`
//!
//! * `rb_id2name`: [`Id::name`](value::Id::name).
// * `rb_id2str`:
// * `RB_ID2SYM`:
//! * `rb_id2sym`: [`std::convert::From`].
// * `rb_id_attrset`:
// * `RB_IMMEDIATE_P`:
//! * `rb_include_module`: [`Module::include_module`].
//! * `rb_inspect`: [`Value::inspect`] or [`std::fmt::Debug`].
// * `rb_int2big`:
// * `RB_INT2FIX`:
// * `rb_int2inum`:
// * `RB_INT2NUM`:
// * `rb_int2num_inline`:
// * `rb_Integer`:
// * `rb_integer_pack`:
// * `rb_integer_type_p`:
// * `rb_integer_unpack`:
//! * `rb_intern`: [`std::convert::From`].
//! * `rb_intern2`: [`std::convert::From`].
//! * `rb_intern3`: [`std::convert::From`].
// * `rb_interned_str`:
// * `rb_interned_str_cstr`:
// * `rb_intern_const`:
//! * `rb_intern_str`: [`std::convert::From`].
// * `rb_interrupt`:
// * `rb_int_new`:
// * `rb_int_pair_to_real`:
// * `rb_int_positive_pow`:
// * `rb_invalid_str`:
//!
//! ## `rb_io`
//!
// * `rb_io_addstr`:
// * `rb_io_ascii8bit_binmode`:
// * `rb_io_binmode`:
// * `rb_io_bufwrite`:
// * `rb_io_check_byte_readable`:
// * `rb_io_check_char_readable`:
// * `rb_io_check_closed`:
// * `rb_io_check_initialized`:
// * `rb_io_check_io`:
// * `rb_io_check_readable`:
// * `rb_io_check_writable`:
// * `rb_io_close`:
// * `rb_io_descriptor`:
// * `rb_io_eof`:
// * `rb_io_extract_encoding_option`:
// * `rb_io_extract_modeenc`:
// * `rb_io_fdopen`:
// * `rb_io_flush`:
// * `rb_io_fptr_finalize`:
// * `rb_io_getbyte`:
// * `rb_io_gets`:
// * `rb_io_get_io`:
// * `rb_io_get_write_io`:
// * `rb_io_make_open_file`:
// * `rb_io_maybe_wait`:
// * `rb_io_maybe_wait_readable`:
// * `rb_io_maybe_wait_writable`:
// * `rb_io_modestr_fmode`:
// * `rb_io_modestr_oflags`:
// * `rb_io_oflags_fmode`:
// * `RB_IO_OPEN`:
// * `RB_IO_POINTER`:
// * `rb_io_print`:
// * `rb_io_printf`:
// * `rb_io_puts`:
// * `rb_io_read_check`:
// * `rb_io_read_pending`:
// * `rb_io_set_nonblock`:
// * `rb_io_set_write_io`:
// * `rb_io_stdio_file`:
// * `rb_io_synchronized`:
// * `rb_io_ungetbyte`:
// * `rb_io_ungetc`:
// * `rb_io_wait`:
// * `rb_io_write`:
//!
//! ## `rb_is`-`rb_iz`
//!
// * `rb_isalnum`:
// * `rb_isalpha`:
// * `rb_isascii`:
// * `rb_isblank`:
// * `rb_iscntrl`:
// * `rb_isdigit`:
// * `rb_isgraph`:
// * `rb_islower`:
// * `rb_isprint`:
// * `rb_ispunct`:
// * `rb_isspace`:
// * `rb_isupper`:
// * `rb_isxdigit`:
// * `rb_is_absolute_path`:
// * `rb_is_attrset_id`:
// * `rb_is_class_id`:
// * `rb_is_const_id`:
// * `rb_is_global_id`:
// * `rb_is_instance_id`:
// * `rb_is_junk_id`:
// * `rb_is_local_id`:
// * `rb_iter_break`:
// * `rb_iter_break_value`:
// * `rb_ivar_count`:
// * `rb_ivar_defined`:
// * `rb_ivar_foreach`:
//! * `rb_ivar_get`: [`Object::ivar_get`].
//! * `rb_ivar_set`: [`Object::ivar_set`].
// * `rb_iv_get`:
// * `rb_iv_set`:
//!
//! ## `rb_j`-`rb_k`
//!
//! * `rb_jump_tag`: Return [`Error`].
// * `rb_keyword_given_p`:
//!
//! ## `rb_l`
//!
// * `rb_lastline_get`:
// * `rb_lastline_set`:
// * `rb_last_status_get`:
// * `rb_last_status_set`:
// * `RB_LIKELY`:
// * `rb_ll2inum`:
// * `RB_LL2NUM`:
// * `rb_ll2num_inline`:
// * `rb_load`:
// * `rb_loaderror`:
// * `rb_loaderror_with_path`:
// * `rb_load_file`:
// * `rb_load_file_str`:
// * `rb_load_protect`:
// * `rb_locale_charmap`:
//! * `rb_locale_encindex`: [`encoding::Index::locale`].
//! * `rb_locale_encoding`: [`RbEncoding::locale`](encoding::RbEncoding::locale).
// * `rb_locale_str_new`:
// * `rb_locale_str_new_cstr`:
// * `RB_LONG2FIX`:
// * `rb_long2int`:
// * `rb_long2int_inline`:
// * `RB_LONG2NUM`:
// * `rb_long2num_inline`:
//!
//! ## `rb_m`
//!
// * `rb_make_backtrace`:
// * `rb_make_exception`:
// * `rb_mark_hash`:
// * `rb_mark_set`:
// * `rb_mark_tbl`:
// * `rb_mark_tbl_no_pin`:
// * `rb_marshal_define_compat`:
// * `rb_marshal_dump`:
// * `rb_marshal_load`:
// * `rb_match_busy`:
// * `rb_memcicmp`:
// * `rb_memerror`:
// * `rb_memhash`:
// * `rb_memory_id`:
// * `rb_memory_view_available_p`:
// * `rb_memory_view_extract_item_members`:
// * `rb_memory_view_fill_contiguous_strides`:
// * `rb_memory_view_get`:
// * `rb_memory_view_get_item`:
// * `rb_memory_view_get_item_pointer`:
// * `rb_memory_view_init_as_byte_array`:
// * `rb_memory_view_is_column_major_contiguous`:
// * `rb_memory_view_is_contiguous`:
// * `rb_memory_view_is_row_major_contiguous`:
// * `rb_memory_view_item_size_from_format`:
// * `rb_memory_view_parse_item_format`:
// * `rb_memory_view_prepare_item_desc`:
// * `rb_memory_view_register`:
// * `rb_memory_view_release`:
// * `rb_memsearch`:
// * `rb_mem_clear`:
// * `rb_method_basic_definition_p`:
// * `rb_method_boundp`:
// * `rb_method_call`:
// * `rb_method_call_kw`:
// * `rb_method_call_with_block`:
// * `rb_method_call_with_block_kw`:
//! * `rb_module_new`: [`RModule::new`].
//! * `rb_mod_ancestors`: [`Module::ancestors`].
// * `rb_mod_class_variables`:
// * `rb_mod_constants`:
// * `rb_mod_const_at`:
// * `rb_mod_const_missing`:
// * `rb_mod_const_of`:
// * `rb_mod_included_modules`:
// * `rb_mod_include_p`:
// * `rb_mod_init_copy`:
// * `rb_mod_method_arity`:
// * `rb_mod_module_eval`:
// * `rb_mod_module_exec`:
// * `rb_mod_name`:
// * `rb_mod_remove_const`:
// * `rb_mod_remove_cvar`:
// * `rb_mod_syserr_fail`:
// * `rb_mod_syserr_fail_str`:
// * `rb_mod_sys_fail`:
// * `rb_mod_sys_fail_str`:
// * `rb_must_asciicompat`:
// * `rb_mutex_lock`:
// * `rb_mutex_locked_p`:
// * `rb_mutex_new`:
// * `rb_mutex_sleep`:
// * `rb_mutex_synchronize`:
// * `rb_mutex_trylock`:
// * `rb_mutex_unlock`:
//!
//! ## `rb_n`
//!
// * `rb_name_error`:
// * `rb_name_error_str`:
// * `rb_nativethread_lock_destroy`:
// * `rb_nativethread_lock_initialize`:
// * `rb_nativethread_lock_lock`:
// * `rb_nativethread_lock_unlock`:
// * `rb_nativethread_self`:
// * `rb_native_cond_broadcast`:
// * `rb_native_cond_destroy`:
// * `rb_native_cond_initialize`:
// * `rb_native_cond_signal`:
// * `rb_native_cond_timedwait`:
// * `rb_native_cond_wait`:
// * `rb_native_mutex_destroy`:
// * `rb_native_mutex_initialize`:
// * `rb_native_mutex_lock`:
// * `rb_native_mutex_trylock`:
// * `rb_native_mutex_unlock`:
// * `rb_need_block`:
// * `RB_NEGFIXABLE`:
// * `RB_NEWOBJ`:
// * `rb_newobj`:
// * `RB_NEWOBJ_OF`:
// * `rb_newobj_of`:
// * `RB_NIL_P`:
// * `rb_nogvl`:
// * `rb_notimplement`:
// * `rb_num2char_inline`:
// * `RB_NUM2CHR`:
// * `rb_num2dbl`:
// * `rb_num2fix`:
// * `RB_NUM2INT`:
// * `rb_num2int`:
// * `rb_num2int_inline`:
// * `RB_NUM2LL`:
// * `rb_num2ll`:
// * `rb_num2ll_inline`:
// * `RB_NUM2LONG`:
// * `rb_num2long`:
// * `rb_num2long_inline`:
// * `RB_NUM2SHORT`:
// * `rb_num2short`:
// * `rb_num2short_inline`:
// * `RB_NUM2SIZE`:
// * `RB_NUM2SSIZE`:
// * `RB_NUM2UINT`:
// * `rb_num2uint`:
// * `RB_NUM2ULL`:
// * `rb_num2ull`:
// * `rb_num2ull_inline`:
// * `RB_NUM2ULONG`:
// * `rb_num2ulong`:
// * `rb_num2ulong_inline`:
// * `RB_NUM2USHORT`:
// * `rb_num2ushort`:
//! * `rb_num_coerce_bin`: [`Numeric::coerce_bin`].
//! * `rb_num_coerce_bit`: [`Numeric::coerce_bit`].
//! * `rb_num_coerce_cmp`: [`Numeric::coerce_cmp`].
//! * `rb_num_coerce_relop`: [`Numeric::coerce_relop`].
// * `rb_num_zerodiv`:
//!
//! ## `rb_o`
//!
// * `rb_obj_alloc`:
//! * `rb_obj_as_string`: [`Value::to_r_string`].
// * `rb_obj_call_init`:
// * `rb_obj_call_init_kw`:
// * `rb_obj_class`:
//! * `rb_obj_classname`: [`Value::classname`].
// * `rb_obj_clone`:
// * `rb_obj_dup`:
// * `rb_obj_encoding`:
// * `RB_OBJ_FREEZE`:
//! * `rb_obj_freeze`: [`Value::freeze`].
// * `rb_obj_freeze_inline`:
// * `RB_OBJ_FREEZE_RAW`:
// * `RB_OBJ_FROZEN`:
// * `rb_obj_frozen_p`:
// * `RB_OBJ_FROZEN_RAW`:
// * `rb_obj_hide`:
// * `rb_obj_id`:
// * `RB_OBJ_INIT_COPY`:
// * `rb_obj_init_copy`:
// * `rb_obj_instance_eval`:
// * `rb_obj_instance_exec`:
// * `rb_obj_instance_variables`:
// * `rb_obj_is_fiber`:
// * `rb_obj_is_instance_of`:
//! * `rb_obj_is_kind_of`: [`Value::is_kind_of`].
// * `rb_obj_is_method`:
//! * `rb_obj_is_proc`: [`Proc::from_value`](block::Proc::from_value).
// * `rb_obj_method`:
// * `rb_obj_method_arity`:
// * `RB_OBJ_PROMOTED`:
// * `RB_OBJ_PROMOTED_RAW`:
// * `rb_obj_remove_instance_variable`:
//! * `rb_obj_respond_to`: [`Value::respond_to`].
// * `rb_obj_reveal`:
// * `rb_obj_setup`:
// * `RB_OBJ_SHAREABLE_P`:
// * `rb_obj_singleton_methods`:
// * `RB_OBJ_WB_UNPROTECT`:
// * `rb_obj_wb_unprotect`:
// * `RB_OBJ_WB_UNPROTECT_FOR`:
// * `RB_OBJ_WRITE`:
// * `RB_OBJ_WRITTEN`:
// * `rb_out_of_int`:
//!
//! ## `rb_p`
//!
// * `rb_p`:
// * `rb_path2class`:
// * `rb_path_check`:
// * `rb_path_to_class`:
// * `rb_pipe`:
// * `RB_POSFIXABLE`:
// * `rb_postponed_job_register`:
// * `rb_postponed_job_register_one`:
// * `rb_prepend_module`: [`Module::prepend_module`].
//! * `rb_proc_arity`: [`Proc::arity`](block::Proc::arity).
//! * `rb_proc_call`: [`Proc::call`](block::Proc::call).
// * `rb_proc_call_kw`:
// * `rb_proc_call_with_block`:
// * `rb_proc_call_with_block_kw`:
// * `rb_proc_exec`:
//! * `rb_proc_lambda_p`: [`Proc::is_lambda`](block::Proc::is_lambda).
//! * `rb_proc_new`: [`Proc::new`](block::Proc::new) & [`Proc::from_fn`](block::Proc::from_fn).
// * `rb_proc_times`:
// * `rb_profile_frames`:
// * `rb_profile_frame_absolute_path`:
// * `rb_profile_frame_base_label`:
// * `rb_profile_frame_classpath`:
// * `rb_profile_frame_first_lineno`:
// * `rb_profile_frame_full_label`:
// * `rb_profile_frame_label`:
// * `rb_profile_frame_method_name`:
// * `rb_profile_frame_path`:
// * `rb_profile_frame_qualified_method_name`:
// * `rb_profile_frame_singleton_method_p`:
//! * `rb_protect`: Called internally by Magnus when required. Available as
//!   [`rb_sys::protect`] with `rb-sys-interop` feature for calling raw Ruby api.
// * `rb_provide`:
// * `rb_provided`:
//!
//! ## `rb_r`
//!
// * `rb_ractor_local_storage_ptr`:
// * `rb_ractor_local_storage_ptr_newkey`:
// * `rb_ractor_local_storage_ptr_set`:
// * `rb_ractor_local_storage_value`:
// * `rb_ractor_local_storage_value_lookup`:
// * `rb_ractor_local_storage_value_newkey`:
// * `rb_ractor_local_storage_value_set`:
// * `rb_ractor_make_shareable`:
// * `rb_ractor_make_shareable_copy`:
// * `rb_ractor_shareable_p`:
// * `rb_ractor_stderr`:
// * `rb_ractor_stderr_set`:
// * `rb_ractor_stdin`:
// * `rb_ractor_stdin_set`:
// * `rb_ractor_stdout`:
// * `rb_ractor_stdout_set`:
//! * `rb_raise`: Simmilar to returning [`Error`].
// * `rb_random_base_init`:
// * `rb_random_bytes`:
// * `RB_RANDOM_DATA_INIT_PARENT`:
// * `rb_random_int32`:
// * `RB_RANDOM_INTERFACE_DECLARE`:
// * `RB_RANDOM_INTERFACE_DECLARE_WITH_REAL`:
// * `RB_RANDOM_INTERFACE_DEFINE`:
// * `RB_RANDOM_INTERFACE_DEFINE_WITH_REAL`:
// * `rb_random_mark`:
// * `RB_RANDOM_PARENT`:
// * `rb_random_real`:
// * `rb_random_ulong_limited`:
// * `rb_rand_bytes_int32`:
// * `rb_rand_if`:
//! * `rb_range_beg_len`: [`Range::beg_len`].
// * `rb_range_new`: [`Range::new`].
// * `rb_range_values`:
// * `rb_Rational`:
// * `rb_Rational1`:
// * `rb_Rational2`:
//! * `rb_rational_den`: [`RRational::den`].
//! * `rb_rational_new`: [`RRational::new`].
// * `rb_rational_new1`:
// * `rb_rational_new2`:
//! * `rb_rational_num`: [`RRational::num`].
// * `rb_rational_raw`:
// * `rb_rational_raw1`:
// * `rb_rational_raw2`:
// * `rb_readwrite_syserr_fail`:
// * `rb_readwrite_sys_fail`:
// * `RB_REALLOC_N`:
// * `rb_refinement_new`:
// * `rb_reg_adjust_startpos`:
// * `rb_reg_alloc`:
//! * `rb_reg_backref_number`: [`RMatch::backref_number`].
// * `rb_reg_init_str`:
//! * `rb_reg_last_match`: [`RMatch::matched`].
//! * `rb_reg_match`: [`RRegexp::reg_match`].
// * `rb_reg_match2`:
//! * `rb_reg_match_last`: [`RMatch::last`].
//! * `rb_reg_match_post`: [`RMatch::post`].
//! * `rb_reg_match_pre`: [`RMatch::pre`].
//! * `rb_reg_new`: See [`RRegexp::new`].
//! * `rb_reg_new_str`: [`RRegexp::new_str`].
//! * `rb_reg_nth_defined`: [`RMatch::nth_defined`].
//! * `rb_reg_nth_match`: [`RMatch::nth_match`].
//! * `rb_reg_options`: [`RRegexp::options`].
// * `rb_reg_prepare_re`:
// * `rb_reg_quote`:
// * `rb_reg_regcomp`:
// * `rb_reg_region_copy`:
// * `rb_reg_regsub`:
// * `rb_reg_search`:
// * `rb_remove_event_hook`:
// * `rb_remove_event_hook_with_data`:
// * `rb_remove_method`:
// * `rb_remove_method_id`:
//! * `rb_require`: [`require`].
//! * `rb_require_string`: [`require`].
// * `rb_rescue`:
// * `rb_rescue2`:
// * `RB_RESERVED_FD_P`:
// * `rb_reserved_fd_p`:
// * `rb_reset_random_seed`:
// * `rb_respond_to`:
// * `rb_ruby_debug_ptr`:
// * `rb_ruby_verbose_ptr`:
//!
//! # `rb_s`-`rb_strl`
//!
//! * `rb_scan_args`: [`scan_args::scan_args`].
// * `rb_scan_args_bad_format`:
// * `rb_scan_args_kw`:
// * `rb_scan_args_length_mismatch`:
// * `rb_set_class_path`:
// * `rb_set_class_path_string`:
// * `rb_set_end_proc`:
// * `rb_set_errinfo`:
//! * `rb_singleton_class`: [`Object::singleton_class`].
// * `rb_singleton_class_attached`:
// * `rb_singleton_class_clone`:
// * `RB_SIZE2NUM`:
// * `rb_sourcefile`:
// * `rb_sourceline`:
// * `rb_spawn`:
// * `rb_spawn_err`:
// * `RB_SPECIAL_CONST_P`:
// * `rb_special_const_p`:
// * `rb_sprintf`:
// * `RB_SSIZE2NUM`:
// * `RB_ST2FIX`:
// * `RB_STATIC_SYM_P`:
// * `rb_stat_new`:
// * `rb_str2inum`:
// * `rb_String`:
// * `rb_string_value`:
// * `rb_string_value_cstr`:
// * `rb_string_value_ptr`:
// * `rb_strlen_lit`:
//!
//! # `rb_struct`
//!
// * `rb_struct_alloc`: See [`RClass::new_instance`].
// * `rb_struct_alloc_noinit`:
//! * `rb_struct_aref`: [`RStruct::aref`].
//! * `rb_struct_aset`: [`RStruct::aset`].
//! * `rb_struct_define`: [`r_struct::define_struct`].
// * `rb_struct_define_under`:
// * `rb_struct_define_without_accessor`:
// * `rb_struct_define_without_accessor_under`:
//! * `rb_struct_getmember`: [`RStruct::getmember`].
// * `rb_struct_initialize`:
//! * `rb_struct_members`: [`RStruct::members`].
//! * `rb_struct_new`: See [`RClass::new_instance`].
// * `rb_struct_ptr`:
//! * `rb_struct_size`: [`RStruct::size`].
// * `rb_struct_s_members`:
//!
//! ## `rb_str`
//!
// * `rb_str_append`:
//! * `rb_str_buf_append`: [`RString::buf_append`].
//! * `rb_str_buf_cat`: [`RString::cat`].
//! * `rb_str_buf_cat_ascii`: See [`RString::cat`].
//! * `rb_str_buf_new`: [`RString::buf_new`].
//! * `rb_str_buf_new_cstr`: See [`RString::buf_new`] + [`RString::cat`].
//! * `rb_str_capacity`: [`RString::capacity`].
//! * `rb_str_cat`: [`RString::cat`].
// * `rb_str_catf`:
//! * `rb_str_cat_cstr`: See [`RString::cat`].
//! * `rb_str_cmp`: [`RString::cmp`].
// * `rb_str_coderange_scan_restartable`:
// * `rb_str_comparable`: [`RString::comparable`].
// * `rb_str_concat`:
//! * `rb_str_conv_enc`: [`RString::conv_enc`].
// * `rb_str_conv_enc_opts`:
//! * `rb_str_drop_bytes`: [`RString::drop_bytes`].
//! * `rb_str_dump`: [`RString::dump`].
// * `rb_str_dup`:
//! * `rb_str_dup_frozen`: See [`RString::new_frozen`].
//! * `rb_str_ellipsize`: [`RString::ellipsize`].
// * `rb_str_encode`:
// * `rb_str_encode_ospath`:
// * `rb_str_equal`:
// * `rb_str_export`:
// * `rb_str_export_locale`:
// * `rb_str_export_to_enc`:
// * `rb_str_format`:
// * `rb_str_free`:
// * `rb_str_freeze`:
// * `rb_str_hash`:
// * `rb_str_hash_cmp`:
// * `rb_str_inspect`:
// * `rb_str_intern`:
// * `rb_str_length`:
// * `rb_str_locktmp`:
// * `rb_str_modify`:
// * `rb_str_modify_expand`:
//! * `rb_str_new`: [`RString::from_slice`].
// * `rb_str_new_cstr`:
//! * `rb_str_new_frozen`: [`RString::new_frozen`].
//! * `rb_str_new_lit`: Simmilar to [`r_string!`].
//! * `rb_str_new_literal`: Simmilar to [`r_string!`].
//! * `rb_str_new_shared`: [`RString::new_shared`].
// * `rb_str_new_static`: Simmilar to [`r_string!`].
// * `rb_str_new_with_class`:
//! * `rb_str_offset`: [`RString::offset`].
//! * `rb_str_plus`: [`RString::plus`].
//! * `rb_str_replace`: [`RString::replace`].
// * `rb_str_resize`:
// * `rb_str_resurrect`:
//! * `rb_str_scrub`: [`RString::scrub`].
// * `rb_str_setter`:
// * `rb_str_set_len`:
//! * `rb_str_shared_replace`: [`RString::shared_replace`].
//! * `rb_str_split`: [`RString::split`].
//! * `rb_str_strlen`: [`RString::length`].
// * `rb_str_sublen`:
// * `rb_str_subpos`:
// * `rb_str_subseq`:
// * `rb_str_substr`:
// * `rb_str_succ`:
//! * `rb_str_times`: [`RString::times`].
// * `rb_str_tmp_new`:
// * `rb_str_to_dbl`:
//! * `rb_str_to_interned_str`: [`RString::to_interned_str`].
// * `rb_str_to_inum`:
//! * `rb_str_to_str`: [`TryConvert`] or [`Value::try_convert`].
// * `rb_str_unlocktmp`:
//! * `rb_str_update`: [`RString::update`].
// * `rb_str_vcatf`:
//!
//! # `rb_st_`
//!
// * `rb_st_add_direct`:
// * `rb_st_cleanup_safe`:
// * `rb_st_clear`:
// * `rb_st_copy`:
// * `rb_st_delete`:
// * `rb_st_delete_safe`:
// * `rb_st_foreach`:
// * `rb_st_foreach_check`:
// * `rb_st_foreach_safe`:
// * `rb_st_foreach_with_replace`:
// * `rb_st_free_table`:
// * `rb_st_get_key`:
// * `rb_st_hash`:
// * `rb_st_hash_end`:
// * `rb_st_hash_start`:
// * `rb_st_hash_uint`:
// * `rb_st_hash_uint32`:
// * `rb_st_init_numtable`:
// * `rb_st_init_numtable_with_size`:
// * `rb_st_init_strcasetable`:
// * `rb_st_init_strcasetable_with_size`:
// * `rb_st_init_strtable`:
// * `rb_st_init_strtable_with_size`:
// * `rb_st_init_table`:
// * `rb_st_init_table_with_size`:
// * `rb_st_insert`:
// * `rb_st_insert2`:
// * `rb_st_keys`:
// * `rb_st_keys_check`:
// * `rb_st_locale_insensitive_strcasecmp`:
// * `rb_st_locale_insensitive_strncasecmp`:
// * `rb_st_lookup`:
// * `rb_st_memsize`:
// * `rb_st_numcmp`:
// * `rb_st_numhash`:
// * `rb_st_shift`:
// * `rb_st_update`:
// * `rb_st_values`:
// * `rb_st_values_check`:
//!
//! ## `rb_sy`-`rb_sz`
//!
// * `RB_SYM2ID`:
//! * `rb_sym2id`: [`std::convert::From`].
//! * `rb_sym2str`: [`Symbol::name`].
// * `RB_SYMBOL_P`:
// * `rb_symname_p`:
// * `rb_sym_all_symbols`:
// * `rb_sym_to_s`:
// * `rb_syserr_fail`:
// * `rb_syserr_fail_str`:
// * `rb_syserr_new`:
// * `rb_syserr_new_str`:
// * `rb_syswait`:
// * `rb_sys_fail`:
// * `rb_sys_fail_str`:
// * `rb_sys_warning`:
//!
//! ## `rb_t`
//!
//! * `RB_TEST`: [`Value::to_bool`] / [`TryConvert`] / [`Value::try_convert`].
// * `rb_thread_add_event_hook`:
// * `rb_thread_add_event_hook2`:
// * `rb_thread_alone`:
// * `rb_thread_atfork`:
// * `rb_thread_atfork_before_exec`:
// * `rb_thread_call_without_gvl`:
// * `rb_thread_call_without_gvl2`:
// * `rb_thread_call_with_gvl`:
// * `rb_thread_check_ints`:
// * `rb_thread_create`:
// * `rb_thread_current`:
// * `rb_thread_fd_close`:
// * `rb_thread_fd_select`:
// * `rb_thread_fd_writable`:
// * `rb_thread_interrupted`:
// * `rb_thread_kill`:
// * `rb_thread_local_aref`:
// * `rb_thread_local_aset`:
// * `rb_thread_main`:
// * `rb_thread_remove_event_hook`:
// * `rb_thread_remove_event_hook_with_data`:
// * `rb_thread_run`:
// * `rb_thread_schedule`:
// * `rb_thread_sleep`:
// * `rb_thread_sleep_deadly`:
// * `rb_thread_sleep_forever`:
// * `rb_thread_stop`:
// * `rb_thread_wait_fd`:
// * `rb_thread_wait_for`:
// * `rb_thread_wakeup`:
// * `rb_thread_wakeup_alive`:
// * `rb_throw`:
// * `rb_throw_obj`:
// * `rb_timespec_now`:
// * `rb_time_interval`:
// * `rb_time_nano_new`:
// * `rb_time_new`:
// * `rb_time_num_new`:
// * `rb_time_timespec`:
// * `rb_time_timespec_interval`:
// * `rb_time_timespec_new`:
// * `rb_time_timeval`:
// * `rb_time_utc_offset`:
// * `rb_tolower`:
// * `rb_toupper`:
//! * `rb_to_encoding`: [`TryConvert`] or [`Value::try_convert`].
//! * `rb_to_encoding_index`: [`TryConvert`] or [`Value::try_convert`].
//! * `rb_to_float`: [`TryConvert`] or [`Value::try_convert`].
// * `rb_to_id`:
//! * `rb_to_int`: [`TryConvert`] or [`Value::try_convert`].
//! * `rb_to_symbol`: [`std::convert::From`].
// * `rb_tracearg_binding`:
// * `rb_tracearg_callee_id`:
// * `rb_tracearg_defined_class`:
// * `rb_tracearg_event`:
// * `rb_tracearg_event_flag`:
// * `rb_tracearg_from_tracepoint`:
// * `rb_tracearg_lineno`:
// * `rb_tracearg_method_id`:
// * `rb_tracearg_object`:
// * `rb_tracearg_path`:
// * `rb_tracearg_raised_exception`:
// * `rb_tracearg_return_value`:
// * `rb_tracearg_self`:
// * `rb_tracepoint_disable`:
// * `rb_tracepoint_enable`:
// * `rb_tracepoint_enabled_p`:
// * `rb_tracepoint_new`:
// * `rb_trap_exit`:
// * `rb_type`:
// * `rb_typeddata_inherited_p`:
// * `rb_typeddata_is_kind_of`:
// * `RB_TYPE_P`:
// * `rb_type_p`:
//!
//! ## `rb_u`
//!
// * `rb_uint2big`:
// * `rb_uint2inum`:
// * `RB_UINT2NUM`:
// * `rb_uint2num_inline`:
// * `rb_uint_new`:
// * `rb_ull2inum`:
// * `RB_ULL2NUM`:
// * `rb_ull2num_inline`:
// * `RB_ULONG2NUM`:
// * `rb_ulong2num_inline`:
// * `rb_undef`:
// * `rb_undefine_finalizer`:
//! * `rb_undef_alloc_func`: [`Class::undef_alloc_func`]
// * `rb_undef_method`:
// * `rb_unexpected_type`:
// * `RB_UNLIKELY`:
// * `rb_update_max_fd`:
//! * `rb_usascii_encindex`: [`encoding::Index::usascii`].
//! * `rb_usascii_encoding`:
//!   [`RbEncoding::usascii`](encoding::RbEncoding::usascii).
// * `rb_usascii_str_new`:
// * `rb_usascii_str_new_cstr`:
// * `rb_usascii_str_new_lit`:
// * `rb_usascii_str_new_literal`:
// * `rb_usascii_str_new_static`:
//! * `rb_utf8_encindex`: [`encoding::Index::utf8`].
//! * `rb_utf8_encoding`: [`RbEncoding::utf8`](encoding::RbEncoding::utf8).
//! * `rb_utf8_str_new`: [`RString::new`].
//! * `rb_utf8_str_new_cstr`: See [`RString::new`].
//! * `rb_utf8_str_new_lit`: Simmilar to [`r_string!`].
//! * `rb_utf8_str_new_literal`: Simmilar to [`r_string!`].
//! * `rb_utf8_str_new_static`: [`r_string!`].
// * `rb_uv_to_utf8`:
//!
//! ## `rb_v`-`rb_z`
//!
// * `rb_vrescue2`:
// * `rb_vsprintf`:
// * `rb_w32_fd_copy`:
// * `rb_w32_fd_dup`:
// * `rb_waitpid`:
// * `rb_warn`:
//! * `rb_warning`: [`error::warning`].
// * `rb_write_error`:
// * `rb_write_error2`:
//! * `rb_yield`: [`block::yield_value`] / return [`block::Yield`].
// * `rb_yield_block`:
//! * `rb_yield_splat`: [`block::yield_splat`] / return [`block::YieldSplat`].
// * `rb_yield_splat_kw`:
//! * `rb_yield_values`:
//!   See [`block::yield_values`] / return [`block::YieldValues`].
//! * `rb_yield_values2`:
//!   [`block::yield_values`] / return [`block::YieldValues`].
// * `rb_yield_values_kw`:
// * `RB_ZALLOC`:
// * `RB_ZALLOC_N`:
//!
//! ## `rc`-`rt`
//!
// * `RCLASS`:
// * `RCLASS_SUPER`:
// * `RDATA`:
// * `RETURN_ENUMERATOR`:
// * `RETURN_ENUMERATOR_KW`:
// * `RETURN_SIZED_ENUMERATOR`:
// * `RETURN_SIZED_ENUMERATOR_KW`:
// * `RFILE`:
// * `RHASH_EMPTY_P`:
// * `RHASH_SET_IFNONE`:
// * `RHASH_SIZE`:
// * `RHASH_TBL`:
// * `RMATCH`:
// * `RMATCH_REGS`:
// * `RMODULE`:
// * `ROBJECT`:
// * `ROBJECT_IVPTR`:
// * `ROBJECT_NUMIV`:
// * `RREGEXP`:
// * `RREGEXP_PTR`:
// * `RREGEXP_SRC`:
// * `RREGEXP_SRC_END`:
// * `RREGEXP_SRC_LEN`:
// * `RREGEXP_SRC_PTR`:
//! * `RSTRING`: Similar to [`RString::from_value`].
//! * `RSTRING_EMBED_LEN`: Similar to [`RString::len`].
// * `RSTRING_END`:
// * `RSTRING_GETMEM`:
//! * `RSTRING_LEN`: [`RString::len`].
//! * `RSTRING_LENINT`: [`RString::len`].
//! * `RSTRING_PTR`: Similar to [`RString::as_str`] and [`RString::as_slice`].
// * `RSTRUCT_GET`:
// * `RSTRUCT_LEN`:
// * `RSTRUCT_SET`:
//! * `RTEST`: [`Value::to_bool`] / [`TryConvert`] / [`Value::try_convert`].
// * `RTYPEDDATA`:
// * `RTYPEDDATA_DATA`:
// * `RTYPEDDATA_P`:
// * `RTYPEDDATA_TYPE`:
//!
//! ## `ruby_`
//!
// * `RUBY_ALIGNAS`:
// * `RUBY_ALIGNOF`:
// * `RUBY_ASSERT`:
// * `RUBY_ASSERT_ALWAYS`:
// * `RUBY_ASSERT_FAIL`:
// * `RUBY_ASSERT_MESG`:
// * `RUBY_ASSERT_MESG_WHEN`:
// * `RUBY_ASSERT_NDEBUG`:
// * `RUBY_ASSERT_WHEN`:
// * `RUBY_ATOMIC_ADD`:
// * `RUBY_ATOMIC_CAS`:
// * `RUBY_ATOMIC_DEC`:
// * `RUBY_ATOMIC_EXCHANGE`:
// * `RUBY_ATOMIC_FETCH_ADD`:
// * `RUBY_ATOMIC_FETCH_SUB`:
// * `RUBY_ATOMIC_INC`:
// * `RUBY_ATOMIC_OR`:
// * `RUBY_ATOMIC_PTR_CAS`:
// * `RUBY_ATOMIC_PTR_EXCHANGE`:
// * `RUBY_ATOMIC_SET`:
// * `RUBY_ATOMIC_SIZE_ADD`:
// * `RUBY_ATOMIC_SIZE_CAS`:
// * `RUBY_ATOMIC_SIZE_DEC`:
// * `RUBY_ATOMIC_SIZE_EXCHANGE`:
// * `RUBY_ATOMIC_SIZE_INC`:
// * `RUBY_ATOMIC_SIZE_SUB`:
// * `RUBY_ATOMIC_SUB`:
// * `RUBY_ATOMIC_VALUE_CAS`:
// * `RUBY_ATOMIC_VALUE_EXCHANGE`:
// * `ruby_brace_glob`:
//! * `ruby_cleanup`: See [`embed::init`] and [`embed::Cleanup`].
// * `RUBY_DEBUG`:
// * `ruby_debug`:
// * `ruby_default_signal`:
// * `ruby_each_words`:
// * `ruby_enc_find_basename`:
// * `ruby_enc_find_extname`:
// * `ruby_executable_node`:
// * `ruby_exec_node`:
// * `ruby_finalize`:
// * `ruby_getcwd`:
// * `ruby_glob`:
// * `ruby_incpush`:
// * `ruby_init`:
// * `ruby_init_loadpath`:
// * `RUBY_INIT_STACK`:
// * `ruby_init_stack`:
// * `ruby_malloc_size_overflow`:
// * `RUBY_METHOD_FUNC`:
// * `ruby_native_thread_p`:
// * `RUBY_NDEBUG`:
// * `ruby_options`:
// * `ruby_posix_signal`:
// * `ruby_process_options`:
// * `ruby_prog_init`:
// * `ruby_qsort`:
// * `ruby_run_node`:
// * `ruby_scan_digits`:
// * `ruby_scan_hex`:
// * `ruby_scan_oct`:
//! * `ruby_script`: Similar to [`embed::ruby_script`].
// * `ruby_setenv`:
//! * `ruby_setup`: [`embed::setup`].
// * `ruby_set_argv`:
//! * `ruby_set_script_name`: [`embed::ruby_script`].
// * `ruby_show_copyright`:
// * `ruby_show_version`:
// * `ruby_signal_name`:
// * `ruby_sig_finalize`:
// * `ruby_snprintf`:
// * `ruby_stack_check`:
// * `ruby_stack_length`:
// * `ruby_stop`:
// * `ruby_strdup`:
// * `ruby_strtod`:
// * `ruby_strtoul`:
// * `ruby_sysinit`:
// * `ruby_unsetenv`:
// * `ruby_verbose`:
// * `ruby_vm_at_exit`:
// * `ruby_vm_destruct`:
// * `ruby_vsnprintf`:
// * `ruby_xcalloc`:
// * `ruby_xfree`:
// * `ruby_xmalloc`:
// * `ruby_xmalloc2`:
// * `ruby_xrealloc`:
// * `ruby_xrealloc2`:
//!
//! ## S-Z
//!
// * `setproctitle`:
// * `set_little_endian_p`:
// * `set_native_size_p`:
// * `StringValue`:
// * `StringValueCStr`:
// * `StringValuePtr`:
// * `st_locale_insensitive_strcasecmp`:
// * `st_locale_insensitive_strncasecmp`:
//! * `TypedData_Get_Struct`: See [`wrap`] and [`TypedData`].
//! * `TypedData_Make_Struct`: See [`wrap`] and [`TypedData`].
//! * `TypedData_Wrap_Struct`: See [`wrap`] and [`TypedData`].
//! </details>

#![cfg_attr(docsrs, feature(doc_cfg))]
#![warn(missing_docs)]

#[macro_use]
mod macros;

mod binding;
pub mod block;
pub mod class;
#[cfg(feature = "embed")]
#[cfg_attr(docsrs, doc(cfg(feature = "embed")))]
pub mod embed;
pub mod encoding;
mod enumerator;
pub mod error;
pub mod exception;
mod float;
pub mod gc;
mod integer;
mod into_value;
pub mod method;
pub mod module;
pub mod numeric;
mod object;
/// Traits that commonly should be in scope.
pub mod prelude {
    pub use crate::{
        class::Class as _, encoding::EncodingCapable as _, module::Module as _,
        numeric::Numeric as _, object::Object as _, try_convert::TryConvert as _,
        value::ReprValue as _,
    };
}
mod r_array;
mod r_bignum;
mod r_complex;
mod r_file;
mod r_float;
pub mod r_hash;
mod r_match;
mod r_object;
mod r_rational;
pub mod r_regexp;
pub mod r_string;
pub mod r_struct;
mod r_typed_data;
mod range;
#[cfg(feature = "rb-sys-interop")]
#[cfg_attr(docsrs, doc(cfg(feature = "rb-sys-interop")))]
pub mod rb_sys;
// Not quite ready to be public, but needed to implement IntoValue
#[doc(hidden)]
pub mod ruby_handle;
pub mod scan_args;
pub mod symbol;
mod try_convert;
pub mod typed_data;
pub mod value;

use std::{ffi::CString, mem::transmute, os::raw::c_int};

#[cfg(ruby_lt_2_7)]
use ::rb_sys::rb_require;
#[cfg(ruby_gte_2_7)]
use ::rb_sys::rb_require_string;
use ::rb_sys::{
    rb_backref_get, rb_call_super, rb_current_receiver, rb_define_class, rb_define_global_const,
    rb_define_global_function, rb_define_module, rb_define_variable, rb_errinfo,
    rb_eval_string_protect, rb_set_errinfo, VALUE,
};
pub use magnus_macros::{init, wrap, DataTypeFunctions, TypedData};

#[cfg(ruby_use_flonum)]
pub use crate::value::Flonum;
pub use crate::{
    binding::Binding,
    class::{Class, RClass},
    enumerator::Enumerator,
    error::Error,
    exception::{Exception, ExceptionClass},
    float::Float,
    integer::Integer,
    into_value::{ArgList, IntoValue, IntoValueFromNative},
    module::{Attr, Module, RModule},
    numeric::Numeric,
    object::Object,
    r_array::RArray,
    r_bignum::RBignum,
    r_complex::RComplex,
    r_file::RFile,
    r_float::RFloat,
    r_hash::RHash,
    r_match::RMatch,
    r_object::RObject,
    r_rational::RRational,
    r_regexp::RRegexp,
    r_string::RString,
    r_struct::RStruct,
    r_typed_data::RTypedData,
    range::Range,
    symbol::Symbol,
    try_convert::TryConvert,
    typed_data::{DataType, DataTypeFunctions, TypedData},
    value::{Fixnum, StaticSymbol, Value, QFALSE, QNIL, QTRUE},
};
use crate::{
    error::protect,
    method::Method,
    r_string::IntoRString,
    ruby_handle::RubyHandle,
    value::{private::ReprValue as _, ReprValue},
};

/// Utility to simplify initialising a static with [`std::sync::Once`].
///
/// Similar (but less generally useful) to
/// [`lazy_static!`](https://crates.io/crates/lazy_static) without an external
/// dependency.
///
/// # Examples
///
/// ```
/// use magnus::{class, define_class, memoize, RClass};
///
/// fn foo_class() -> &'static RClass {
///     memoize!(RClass: define_class("Foo", class::object()).unwrap())
/// }
/// ```
#[macro_export]
macro_rules! memoize {
    ($type:ty: $val:expr) => {{
        static INIT: std::sync::Once = std::sync::Once::new();
        static mut VALUE: Option<$type> = None;
        unsafe {
            INIT.call_once(|| {
                VALUE = Some($val);
            });
            VALUE.as_ref().unwrap()
        }
    }};
}

impl RubyHandle {
    pub fn define_class(&self, name: &str, superclass: RClass) -> Result<RClass, Error> {
        debug_assert_value!(superclass);
        let name = CString::new(name).unwrap();
        let superclass = superclass.as_rb_value();
        protect(|| unsafe {
            RClass::from_rb_value_unchecked(rb_define_class(name.as_ptr(), superclass))
        })
    }

    pub fn define_module(&self, name: &str) -> Result<RModule, Error> {
        let name = CString::new(name).unwrap();
        protect(|| unsafe { RModule::from_rb_value_unchecked(rb_define_module(name.as_ptr())) })
    }

    pub fn define_error(
        &self,
        name: &str,
        superclass: ExceptionClass,
    ) -> Result<ExceptionClass, Error> {
        define_class(name, superclass.as_r_class())
            .map(|c| unsafe { ExceptionClass::from_value_unchecked(c.as_value()) })
    }

    pub fn define_variable<T>(&self, name: &str, initial: T) -> Result<*mut Value, Error>
    where
        T: IntoValue,
    {
        let initial = self.into_value(initial);
        debug_assert_value!(initial);
        let name = CString::new(name).unwrap();
        let ptr = Box::into_raw(Box::new(initial));
        unsafe {
            rb_define_variable(name.as_ptr(), ptr as *mut VALUE);
        }
        Ok(ptr)
    }

    pub fn define_global_const<T>(&self, name: &str, value: T) -> Result<(), Error>
    where
        T: IntoValue,
    {
        let value = self.into_value(value);
        let name = CString::new(name).unwrap();
        protect(|| {
            unsafe {
                rb_define_global_const(name.as_ptr(), value.as_rb_value());
            }
            self.qnil()
        })?;
        Ok(())
    }

    pub fn define_global_function<M>(&self, name: &str, func: M)
    where
        M: Method,
    {
        let name = CString::new(name).unwrap();
        unsafe {
            rb_define_global_function(name.as_ptr(), transmute(func.as_ptr()), M::arity().into());
        }
    }

    pub fn backref_get(&self) -> Option<RMatch> {
        unsafe {
            let value = Value::new(rb_backref_get());
            (!value.is_nil()).then(|| RMatch::from_rb_value_unchecked(value.as_rb_value()))
        }
    }

    pub fn current_receiver<T>(&self) -> Result<T, Error>
    where
        T: TryConvert,
    {
        protect(|| unsafe { Value::new(rb_current_receiver()) }).and_then(TryConvert::try_convert)
    }

    pub fn call_super<A, T>(&self, args: A) -> Result<T, Error>
    where
        A: ArgList,
        T: TryConvert,
    {
        unsafe {
            let args = args.into_arg_list();
            let slice = args.as_ref();
            protect(|| {
                Value::new(rb_call_super(
                    slice.len() as c_int,
                    slice.as_ptr() as *const VALUE,
                ))
            })
            .and_then(TryConvert::try_convert)
        }
    }

    #[cfg(ruby_gte_2_7)]
    pub fn require<T>(&self, feature: T) -> Result<bool, Error>
    where
        T: IntoRString,
    {
        let feature = feature.into_r_string_with(self);
        protect(|| unsafe { Value::new(rb_require_string(feature.as_rb_value())) })
            .and_then(TryConvert::try_convert)
    }

    #[cfg(ruby_lt_2_7)]
    pub fn require(&self, feature: &str) -> Result<bool, Error> {
        let feature = CString::new(feature).unwrap();
        protect(|| unsafe { Value::new(rb_require(feature.as_ptr())) })
            .and_then(TryConvert::try_convert)
    }

    pub fn eval<T>(&self, s: &str) -> Result<T, Error>
    where
        T: TryConvert,
    {
        let mut state = 0;
        // safe ffi to Ruby, captures raised errors (+ brake, throw, etc) as state
        let result = unsafe {
            let s = CString::new(s)
                .map_err(|e| Error::new(exception::script_error(), e.to_string()))?;
            rb_eval_string_protect(s.as_c_str().as_ptr(), &mut state as *mut _)
        };

        match state {
            // Tag::None
            0 => T::try_convert(Value::new(result)),
            // Tag::Raise
            6 => unsafe {
                let ex = Exception::from_rb_value_unchecked(rb_errinfo());
                rb_set_errinfo(self.qnil().as_rb_value());
                Err(Error::Exception(ex))
            },
            other => Err(Error::Jump(unsafe { transmute(other) })),
        }
    }
}

/// Define a class in the root scope.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[inline]
pub fn define_class(name: &str, superclass: RClass) -> Result<RClass, Error> {
    get_ruby!().define_class(name, superclass)
}

/// Define a module in the root scope.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[inline]
pub fn define_module(name: &str) -> Result<RModule, Error> {
    get_ruby!().define_module(name)
}

/// Define an exception class in the root scope.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[inline]
pub fn define_error(name: &str, superclass: ExceptionClass) -> Result<ExceptionClass, Error> {
    get_ruby!().define_error(name, superclass)
}

/// Define a global variable.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[inline]
pub fn define_variable<T>(name: &str, initial: T) -> Result<*mut Value, Error>
where
    T: IntoValue,
{
    get_ruby!().define_variable(name, initial)
}

/// Define a global constant.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[inline]
pub fn define_global_const<T>(name: &str, value: T) -> Result<(), Error>
where
    T: IntoValue,
{
    get_ruby!().define_global_const(name, value)
}

/// Define a method in the root scope.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[inline]
pub fn define_global_function<M>(name: &str, func: M)
where
    M: Method,
{
    get_ruby!().define_global_function(name, func)
}

/// Returns the result of the most recent regexp match.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
///
/// # Examples
///
/// ```
/// use magnus::{backref_get, RRegexp};
/// # let _cleanup = unsafe { magnus::embed::init() };
///
/// let regexp = RRegexp::new("b(.)r", Default::default()).unwrap();
/// let result = regexp.reg_match("foo bar baz").unwrap();
/// assert_eq!(result, Some(4));
///
/// let match_data = backref_get().unwrap();
/// assert_eq!(match_data.matched().to_string().unwrap(), String::from("bar"));
/// assert_eq!(match_data.nth_match(1).map(|v| v.to_string().unwrap()), Some(String::from("a")));
/// ```
#[inline]
pub fn backref_get() -> Option<RMatch> {
    get_ruby!().backref_get()
}

/// Return the Ruby `self` of the current method context.
///
/// Returns `Err` if called outside a method context or the conversion fails.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[inline]
pub fn current_receiver<T>() -> Result<T, Error>
where
    T: TryConvert,
{
    get_ruby!().current_receiver()
}

/// Call the super method of the current method context.
///
/// Returns `Ok(T)` if the super method exists and returns without error, and
/// the return value converts to a `T`, or returns `Err` if there is no super
/// method, the super method raises or the conversion fails.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
#[inline]
pub fn call_super<A, T>(args: A) -> Result<T, Error>
where
    A: ArgList,
    T: TryConvert,
{
    get_ruby!().call_super(args)
}

/// Finds and loads the given feature if not already loaded.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
///
/// # Examples
///
/// ```
/// # let _cleanup = unsafe { magnus::embed::init() };
/// use magnus::require;
///
/// assert!(require("net/http").unwrap());
/// ```
#[cfg(ruby_gte_2_7)]
#[inline]
pub fn require<T>(feature: T) -> Result<bool, Error>
where
    T: IntoRString,
{
    get_ruby!().require(feature)
}

/// Finds and loads the given feature if not already loaded.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
///
/// # Examples
///
/// ```
/// # let _cleanup = unsafe { magnus::embed::init() };
/// use magnus::require;
///
/// assert!(require("net/http").unwrap());
/// ```
#[cfg(ruby_lt_2_7)]
#[inline]
pub fn require(feature: &str) -> Result<bool, Error> {
    get_ruby!().require(feature)
}

/// Evaluate a string of Ruby code, converting the result to a `T`.
///
/// Ruby will use the 'ASCII-8BIT' (aka binary) encoding for any Ruby string
/// literals in the passed string of Ruby code. See the
/// [`eval`](macro@crate::eval) macro or [`Binding::eval`] for alternatives that
/// support utf-8.
///
/// Errors if `s` contains a null byte, the conversion fails, or on an uncaught
/// Ruby exception.
///
/// # Panics
///
/// Panics if called from a non-Ruby thread.
///
/// # Examples
///
/// ```
/// # let _cleanup = unsafe { magnus::embed::init() };
///
/// assert_eq!(magnus::eval::<i64>("1 + 2").unwrap(), 3);
/// ```
#[inline]
pub fn eval<T>(s: &str) -> Result<T, Error>
where
    T: TryConvert,
{
    get_ruby!().eval(s)
}
