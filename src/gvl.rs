//! Functions for dealing with the ruby GVL.
//!
//! **BE CAUTIOUS WHEN USING THESE.**
//!
//! Using ANY of these functions from a thread not made by Ruby is UB.
//! You **will** get random segfaults or memory errors.
//!
//! Most of the provided functions exist only to provide type safety.
//! Ruby GVL functions take in void pointers (effectively type erasure) which is easy to get wrong.
//!
//!
//! --- Here be dragons ---
//!
//! On the odd chance you *do* want to use these to run Ruby in threads not made by Ruby, you can try this.
//!
//! The only way to do it is by using message passing or some other mechanism to run Ruby code in a thread made by Ruby.
//! Read [this article](https://www.burgestrand.se/articles/asynchronous-callbacks-in-ruby-c-extensions/) for a good explanation, and look at
//! [libfmod-rb](https://github.com/Speak2Erase/libfmod-rb/blob/master/ext/libfmod_ext/src/callback.rs) for an actual (albiet scuffed) implementation.
use std::ffi::c_void;

/// Type safe wrapper around rb_thread_call_without_gvl.
/// This function is still very unsafe and should be used sparingly.
///
/// Saftey:
///     - This function should not call back into ruby without first reaquiring the GVL.
///     - **NEVER CALL THIS FROM A THREAD NOT MADE BY RUBY**
/// Because it's nigh impossible to check these points, these functions are marked as unsafe.
///
/// Example usage:
///
/// ```
/// fn sleep() -> String {
///     std::thread::sleep(std::time::Duration::from_secs(5));
///
///     "I am finished sleeping!".to_string()
/// }
///
/// fn ruby_sleep() -> String {
///     unsafe {
///         magnus::gvl::without_gvl_no_ubf(|_: ()| {
///             sleep()
///         }, ())
///     }
/// }
///
/// ```
pub unsafe fn without_gvl_no_ubf<Func, FuncArgs, FuncReturn>(
    func: Func,
    func_args: FuncArgs,
) -> FuncReturn
where
    Func: FnOnce(FuncArgs) -> FuncReturn,
{
    unsafe extern "C" fn anon_func<Func, FuncArgs, FuncReturn>(data: *mut c_void) -> *mut c_void
    where
        Func: FnOnce(FuncArgs) -> FuncReturn,
    {
        let (func, func_args): (Func, FuncArgs) = *Box::from_raw(data as *mut (Func, FuncArgs));

        Box::into_raw(Box::new(func(func_args))) as *mut _
    }

    //? SAFETY: We box the function and args to pass them over the FFI boundary.
    let boxed_args = Box::new((func, func_args));

    let result = rb_sys::rb_thread_call_without_gvl(
        Some(anon_func::<Func, FuncArgs, FuncReturn>),
        Box::into_raw(boxed_args) as *mut _,
        None,
        std::ptr::null_mut(),
    );

    *Box::from_raw(result as _)
}

/// Type safe wrapper around rb_thread_call_without_gvl.
/// Takes in a unblocking function.
/// Ruby will call your unblocking function when it recieves an interrupt.
///
/// This function is still very unsafe and should be used sparingly.
///
/// Saftey:
///     - This function should not call back into ruby without first reaquiring the GVL.
///     - **NEVER CALL THIS FROM A THREAD NOT MADE BY RUBY**
///     - The unblocking function should perform any necessary cleanup?
/// Because it's nigh impossible to check these points, these functions are marked as unsafe.
///
/// Example usage:
/// ```
/// fn wait_for_interrput(condvar: &std::sync::Condvar, mutex: &std::sync::Mutex<()>) -> String {
///     let lock = mutex.lock().unwrap();
///
///     condvar.wait(lock).unwrap();
///
///     "The unblocking function just wakes me up, ruby can't just halt this function. I still have to return a result thanks to type safety :)".to_string()
/// }
///
/// fn ruby_wait_for_interrput() -> String {
///     unsafe {
///         let condvar = std::sync::Condvar::new();
///         let mutex = std::sync::Mutex::new(());
///
///         magnus::gvl::without_gvl(
///             |(condvar, mutex)| {
///                 wait_for_interrput(condvar, mutex)
///             },
///             (&condvar, &mutex),
///             |condvar| {
///                 condvar.notify_all();
///             },
///             &condvar
///         )
///     }
/// }
///
/// ```
pub unsafe fn without_gvl<Func, FuncArgs, FuncReturn, Unblock, UnblockArgs>(
    func: Func,
    func_args: FuncArgs,
    unblock: Unblock,
    unblock_args: UnblockArgs,
) -> FuncReturn
where
    Func: FnOnce(FuncArgs) -> FuncReturn,
    Unblock: FnOnce(UnblockArgs),
{
    unsafe extern "C" fn anon_func<Func, FuncArgs, FuncReturn>(data: *mut c_void) -> *mut c_void
    where
        Func: FnOnce(FuncArgs) -> FuncReturn,
    {
        let (func, func_args): (Func, FuncArgs) = *Box::from_raw(data as _);

        Box::into_raw(Box::new(func(func_args))) as _
    }

    unsafe extern "C" fn anon_unblock<Unblock, UnblockArgs>(data: *mut c_void)
    where
        Unblock: FnOnce(UnblockArgs),
    {
        let (func, func_args): (Unblock, UnblockArgs) = *Box::from_raw(data as _);

        func(func_args);
    }

    // Box the function and args to pass them over the FFI boundary.
    let boxed_args = Box::new((func, func_args));
    let boxed_unblock_args = Box::new((unblock, unblock_args));

    let result = rb_sys::rb_thread_call_without_gvl(
        Some(anon_func::<Func, FuncArgs, FuncReturn>),
        Box::into_raw(boxed_args) as *mut _,
        Some(anon_unblock::<Unblock, UnblockArgs>),
        Box::into_raw(boxed_unblock_args) as *mut _,
    );

    *Box::from_raw(result as _)
}

/// Type safe wrapper around rb_thread_call_with_gvl.
/// Reacquires the GVL. Used for calling back into Ruby while inside a GVL releasing function.
///
/// This function is still very unsafe and should be used sparingly.
///
/// Saftey:
///     - **NEVER CALL THIS FROM A THREAD NOT MADE BY RUBY**
///     - Don't call this function while holding the GVL.
/// Because it's nigh impossible to check these points, these functions are marked as unsafe.
///
/// Example usage:
/// ```
/// fn ruby_wait_and_call(time: f64) -> Result<magnus::Value, magnus::Error> {
///     let block = magnus::block::block_proc()?;
///
///     unsafe {
///         magnus::gvl::without_gvl_no_ubf(|(time, block)| {
///             std::thread::sleep(std::time::Duration::from_secs_f64(time));
///
///             // If we didn't reacquire the GVL here, we'd likely get a segfault!!!
///             unsafe {
///                 magnus::gvl::with_gvl(|block| {
///                     block.call(())
///                 }, block)
///             }
///         }, (time, block))
///     }
/// }
/// ```
pub unsafe fn with_gvl<Func, FuncArgs, FuncReturn>(func: Func, func_args: FuncArgs) -> FuncReturn
where
    Func: FnOnce(FuncArgs) -> FuncReturn,
{
    unsafe extern "C" fn anon_func<Func, FuncArgs, FuncReturn>(data: *mut c_void) -> *mut c_void
    where
        Func: FnOnce(FuncArgs) -> FuncReturn,
    {
        let (func, func_args): (Func, FuncArgs) = *Box::from_raw(data as *mut (Func, FuncArgs));

        Box::into_raw(Box::new(func(func_args))) as *mut _
    }

    // Box the function and args to pass them over the FFI boundary.
    let boxed_args = Box::new((func, func_args));

    let result = rb_sys::rb_thread_call_with_gvl(
        Some(anon_func::<Func, FuncArgs, FuncReturn>),
        Box::into_raw(boxed_args) as *mut _,
    );

    *Box::from_raw(result as _)
}
