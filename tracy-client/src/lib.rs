//! This crate is a set of safe bindings to the client library of the [Tracy profiler].
//!
//! If you have already instrumented your application with `tracing`, consider the `tracing-tracy`
//! crate.
//!
//! [Tracy profiler]: https://github.com/wolfpld/tracy
//!
//! # Important note
//!
//! Depending on the configuration Tracy may broadcast discovery packets to the local network and
//! expose the data it collects in the background to that same network. Traces collected by Tracy
//! may include source and assembly code as well.
//!
//! As thus, you may want make sure to only enable the `tracy-client` crate conditionally, via
//! the `enable` feature flag provided by this crate.
//!
//! In order to start tracing it is important that you first call the [`enable`] function first to
//! initialize the client. The [`disable`] must not be called until it is guaranteed that there
//! will be no more calls to any other APIs. This can be especially difficult to ensure if you have
//! detached threads. It is valid to never call `disable` at all.
//!
//! # Features
//!
//! Refer to the [`sys`] crate for documentation on crate features. This crate re-exports all the
//! features from [`sys`].
#![cfg_attr(not(feature = "enable"), allow(unused_imports, unused_variables))]

use std::alloc;
use std::ffi::CString;
use std::sync::atomic::{AtomicUsize, Ordering};
pub use sys;

/// When enabling `Tracy` when it is already enabled, or when disabling when it is already disabled
/// can cause applications to crash. I personally think it would be better if this was a sort-of
/// reference counted kind-of thing so you could enable as many times as you wish and disable just
/// as many times without any reprecursions. At the very least this could significantly help tests.
///
/// In order to do this we want to track 4 states that construct a following finite state machine
///
/// ```text
///     0 = disabled  -----> 1 = enabling
///         ^                    v
///     3 = disabling <----- 2 = enabled
/// ```
///
/// And also include a reference count somewhere in there. Something we can throw in a static would
/// be ideal.
///
/// Sadly, I am not aware of any libraries which would make this easier, so rolling out our own
/// things it is then!
///
/// Oh and it'll definitely involve spinning, getting some vertigo medication is advised.
///
/// ---
///
/// We will use a single Atomic to store this information. The 2 top-most bits will represent the
/// state bits and the rest will act as a counter.
#[cfg(feature = "enable")]
static ENABLE_STATE: AtomicUsize = AtomicUsize::new(0);
#[cfg(feature = "enable")]
const REFCOUNT_MASK: usize = usize::max_value() >> 2;
#[cfg(feature = "enable")]
const STATE_STEP: usize = REFCOUNT_MASK + 1; // Move forward by 1 step in the FSM
#[cfg(feature = "enable")]
const STATE_DISABLED: usize = 0;
#[cfg(feature = "enable")]
const STATE_ENABLING: usize = STATE_DISABLED + STATE_STEP;
#[cfg(feature = "enable")]
const STATE_ENABLED: usize = STATE_ENABLING + STATE_STEP;
#[cfg(feature = "enable")]
const STATE_DISABLING: usize = STATE_ENABLED + STATE_STEP;
#[cfg(feature = "enable")]
const STATE_MASK: usize = STATE_DISABLING;

/// Enable the client.
///
/// The client must be enabled with this function before any instrumentation is invoked. This
/// function can be called multiple times to increase the activation count even while the client
/// already has been enabled.
///
/// # Example
///
/// ```rust
/// fn main() {
///     tracy_client::enable();
///     // ...
///     tracy_client::disable();
/// }
pub fn enable() {
    #[cfg(feature = "enable")]
    {
        // We don't particularly care about efficiency here, so we’ll be using CAS loops and
        // orderings that aren't necessarily the fastest possible in this instance.
        let old_state = loop {
            let result = ENABLE_STATE.fetch_update(Ordering::SeqCst, Ordering::SeqCst, |state| {
                // Here we want to increment the reference count, and also apply the tansition from
                // state 0 (disabled) to state 1 (enabling), if possible.
                match state & STATE_MASK {
                    STATE_DISABLED => Some(state + STATE_ENABLING + 1),
                    STATE_ENABLED => Some(state + 1),
                    STATE_ENABLING => Some(state + 1),
                    // Wait for the ongoing disable to complete.
                    STATE_DISABLING => None,
                    _ => unreachable!(),
                }
            });
            if let Ok(result) = result {
                break result;
            }
        };
        match old_state & STATE_MASK {
            STATE_DISABLED => {
                unsafe {
                    // SAFETY: no known soundness invariants.
                    sys::___tracy_startup_profiler();
                }
                ENABLE_STATE.fetch_add(STATE_STEP, Ordering::SeqCst);
            }
            STATE_ENABLING => {
                // wait for the profiler to reach the enabled state
                while ENABLE_STATE.load(Ordering::SeqCst) & STATE_MASK != STATE_ENABLED {}
            }
            STATE_ENABLED => return,
            _ => unreachable!(),
        }
    }
}

/// Disable the client.
///
/// This function will decrease the activation count and unload the client once this count reaches
/// zero. Once the client has been disabled, no other calls to the instrumentation APIs may be
/// made. Note that unloading the client will also discard any data collected up to that point.
///
/// When using threads, especially detached ones, consider either never calling `disable`, or at
/// least use a `enable`-`disable` pair for each thread.
///
/// # Examples
///
/// ```rust
/// fn main() {
///     tracy_client::enable();
///     // ...
///     tracy_client::disable();
/// }
/// ```
///
/// One thing to watch out in particular is drop guards. For example the following code is invalid
/// because a span guard is dropped after `disable` is called.
///
/// ```rust,no_run
/// {
///     tracy_client::enable();
///     let _span = tracy_client::span!("some span");
///     tracy_client::disable();
/// } // `_span` is dropped here, after the client has been disabled!
/// ```
pub fn disable() {
    #[cfg(feature = "enable")]
    {
        let old_state = loop {
            let result = ENABLE_STATE.fetch_update(Ordering::SeqCst, Ordering::SeqCst, |state| {
                match state & STATE_MASK {
                    STATE_DISABLED => Some(state), // no change
                    // last reference, go to the disabling state
                    STATE_ENABLED if state & REFCOUNT_MASK == 1 => Some(STATE_DISABLING),
                    STATE_ENABLED => Some(state - 1),
                    // Wait for an ongoing enable or disable complete.
                    STATE_ENABLING | STATE_DISABLING => None,
                    _ => unreachable!(),
                }
            });
            if let Ok(result) = result {
                break result;
            }
        };
        match old_state & STATE_MASK {
            STATE_ENABLED if old_state & REFCOUNT_MASK == 1 => {
                unsafe {
                    dbg!(sys::___tracy_shutdown_profiler());
                }
                ENABLE_STATE.fetch_and(REFCOUNT_MASK, Ordering::SeqCst);
            }
            STATE_DISABLED | STATE_ENABLED => {}
            STATE_ENABLING | STATE_DISABLING | _ => unreachable!(),
        }
    }
}

/// Start a new Tracy span with function, file, and line information determined automatically.
///
/// # Examples
///
/// Begin a span region, which will be terminated once `_span` goes out of scope:
///
/// ```
/// # tracy_client::enable();
/// let _span = tracy_client::span!("some span");
/// # drop(_span);
/// # tracy_client::disable();
/// ```
#[macro_export]
macro_rules! span {
    ($name:expr) => {
        $crate::span_impl!($name, 62)
    };
    ($name:expr, $callstack_depth:expr) => {
        $crate::span_impl!($name, $callstack_depth)
    };
}

#[macro_export]
#[doc(hidden)]
#[cfg(feature = "enable")]
macro_rules! span_impl {
    ($name:expr, $callstack_depth:expr) => {{
        use std::ffi::CString;
        use $crate::internal::once_cell::sync::Lazy;

        struct S;
        static SRC_LOC: Lazy<$crate::internal::SrcLoc> = Lazy::new(|| {
            let function_name = std::any::type_name::<S>();
            let function_name = CString::new(&function_name[..function_name.len() - 3]).unwrap();
            $crate::internal::SrcLoc {
                data: $crate::sys::___tracy_source_location_data {
                    name: concat!($name, "\0").as_ptr().cast(),
                    function: function_name.as_ptr(),
                    file: concat!(file!(), "\0").as_ptr().cast(),
                    line: line!(),
                    color: 0,
                },
                _function_name: function_name,
            }
        });
        unsafe { $crate::Span::from_src_loc(&SRC_LOC.data, $callstack_depth) }
    }};
}

#[macro_export]
#[doc(hidden)]
#[cfg(not(feature = "enable"))]
macro_rules! span_impl {
    ($name:expr, $callstack_depth:expr) => {
        $crate::Span::disabled()
    };
}

#[doc(hidden)]
#[cfg(feature = "enable")]
pub mod internal {
    use std::ffi::CString;

    pub use once_cell;

    pub struct SrcLoc {
        pub _function_name: CString,
        pub data: sys::___tracy_source_location_data,
    }

    unsafe impl Send for SrcLoc {}
    unsafe impl Sync for SrcLoc {}
}

/// A handle representing a span of execution.
#[cfg(feature = "enable")]
pub struct Span(
    sys::___tracy_c_zone_context,
    std::marker::PhantomData<*mut sys::___tracy_c_zone_context>,
);

#[cfg(not(feature = "enable"))]
pub struct Span(());

impl Span {
    /// Start a new Tracy span.
    ///
    /// This function allocates the span information on the heap until it is read out by the
    /// profiler.
    ///
    /// `callstack_depth` specifies the maximum number of stack frames client should collect.
    pub fn new(name: &str, function: &str, file: &str, line: u32, callstack_depth: u16) -> Self {
        #[cfg(not(feature = "enable"))]
        {
            return Self(());
        }
        #[cfg(feature = "enable")]
        unsafe {
            let loc = sys::___tracy_alloc_srcloc_name(
                line,
                file.as_ptr() as _,
                file.len(),
                function.as_ptr() as _,
                function.len(),
                name.as_ptr() as _,
                name.len(),
            );
            if callstack_depth == 0 {
                Self(
                    sys::___tracy_emit_zone_begin_alloc(loc, 1),
                    std::marker::PhantomData,
                )
            } else {
                Self(
                    sys::___tracy_emit_zone_begin_alloc_callstack(
                        loc,
                        adjust_stack_depth(callstack_depth).into(),
                        1,
                    ),
                    std::marker::PhantomData,
                )
            }
        }
    }

    #[inline]
    #[doc(hidden)]
    #[cfg(not(feature = "enable"))]
    pub fn disabled() -> Self {
        Self(())
    }

    #[inline]
    #[doc(hidden)]
    #[cfg(feature = "enable")]
    pub unsafe fn from_src_loc(
        loc: &'static sys::___tracy_source_location_data,
        callstack_depth: u16,
    ) -> Self {
        if callstack_depth == 0 {
            Self(
                sys::___tracy_emit_zone_begin(loc, 1),
                std::marker::PhantomData,
            )
        } else {
            Self(
                sys::___tracy_emit_zone_begin_callstack(
                    loc,
                    adjust_stack_depth(callstack_depth).into(),
                    1,
                ),
                std::marker::PhantomData,
            )
        }
    }

    /// Emit a numeric value associated with this span.
    pub fn emit_value(&self, value: u64) {
        // SAFE: the only way to construct `Span` is by creating a valid tracy zone context.
        #[cfg(feature = "enable")]
        unsafe {
            sys::___tracy_emit_zone_value(self.0, value);
        }
    }

    /// Emit some text associated with this span.
    pub fn emit_text(&self, text: &str) {
        // SAFE: the only way to construct `Span` is by creating a valid tracy zone context.
        #[cfg(feature = "enable")]
        unsafe {
            sys::___tracy_emit_zone_text(self.0, text.as_ptr() as _, text.len());
        }
    }

    /// Emit a color associated with this span.
    pub fn emit_color(&self, color: u32) {
        // SAFE: the only way to construct `Span` is by creating a valid tracy zone context.
        #[cfg(feature = "enable")]
        unsafe {
            sys::___tracy_emit_zone_color(self.0, color);
        }
    }
}

impl Drop for Span {
    fn drop(&mut self) {
        // SAFE: the only way to construct `Span` is by creating a valid tracy zone context.
        #[cfg(feature = "enable")]
        unsafe {
            sys::___tracy_emit_zone_end(self.0);
        }
    }
}

/// A profiling wrapper around an allocator.
///
/// See documentation for [`std::alloc`](std::alloc) for more information about global allocators.
///
/// Note that for this to work correctly, all allocations freed while the client is enabled must
/// have a corresponding allocation in the same client instance.
///
/// # Examples
///
/// In your executable, add:
///
/// ```rust
/// # use tracy_client::*;
/// #[global_allocator]
/// static GLOBAL: ProfiledAllocator<std::alloc::System> =
///     ProfiledAllocator::new(std::alloc::System, 100);
/// ```
pub struct ProfiledAllocator<T>(T, u16);

impl<T> ProfiledAllocator<T> {
    pub const fn new(inner_allocator: T, callstack_depth: u16) -> Self {
        Self(inner_allocator, adjust_stack_depth(callstack_depth))
    }

    fn emit_alloc(&self, ptr: *mut u8, size: usize) -> *mut u8 {
        #[cfg(feature = "enable")]
        unsafe {
            if self.1 == 0 {
                sys::___tracy_emit_memory_alloc(ptr.cast(), size, 1);
            } else {
                sys::___tracy_emit_memory_alloc_callstack(ptr.cast(), size, self.1.into(), 1);
            }
        }
        ptr
    }

    fn emit_free(&self, ptr: *mut u8) -> *mut u8 {
        #[cfg(feature = "enable")]
        unsafe {
            if self.1 == 0 {
                sys::___tracy_emit_memory_free(ptr.cast(), 1);
            } else {
                sys::___tracy_emit_memory_free_callstack(ptr.cast(), self.1.into(), 1);
            }
        }
        ptr
    }
}

unsafe impl<T: alloc::GlobalAlloc> alloc::GlobalAlloc for ProfiledAllocator<T> {
    unsafe fn alloc(&self, layout: alloc::Layout) -> *mut u8 {
        self.emit_alloc(self.0.alloc(layout), layout.size())
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: alloc::Layout) {
        self.0.dealloc(self.emit_free(ptr), layout)
    }

    unsafe fn alloc_zeroed(&self, layout: alloc::Layout) -> *mut u8 {
        self.emit_alloc(self.0.alloc_zeroed(layout), layout.size())
    }

    unsafe fn realloc(&self, ptr: *mut u8, layout: alloc::Layout, new_size: usize) -> *mut u8 {
        self.emit_alloc(
            self.0.realloc(self.emit_free(ptr), layout, new_size),
            new_size,
        )
    }
}

/// Indicate that rendering of a continuous frame has ended.
///
/// Typically should be inserted after a buffer swap.
///
/// In case you want to annotate secondary continuous frame sets, call the macro with a string
/// argument.
///
/// For non-continuous frame sets see [`Frame`](Frame).
///
/// # Examples
///
/// ```no_run
/// # use tracy_client::*;
/// # fn swap_buffers() {}
/// swap_buffers();
/// finish_continuous_frame!();
/// finish_continuous_frame!("some other frame loop");
/// ```
#[macro_export]
macro_rules! finish_continuous_frame {
    () => {
        unsafe {
            $crate::finish_continuous_frame(std::ptr::null());
        }
    };
    ($name: literal) => {
        unsafe {
            $crate::finish_continuous_frame(concat!($name, "\0").as_ptr() as _);
        }
    };
}

/// Use `finish_continuous_frame!` instead.
///
/// `name` must contain a NULL byte.
#[doc(hidden)]
pub unsafe fn finish_continuous_frame(name: *const u8) {
    #[cfg(feature = "enable")]
    {
        sys::___tracy_emit_frame_mark(name as _);
    }
}

/// Start a non-continuous frame region.
#[macro_export]
macro_rules! start_noncontinuous_frame {
    ($name: literal) => {
        unsafe { $crate::Frame::start_noncontinuous_frame(concat!($name, "\0")) }
    };
}

/// A non-continuous frame region.
///
/// Create with the [`start_noncontinuous_frame`](start_noncontinuous_frame) macro.
pub struct Frame(&'static str);

impl Frame {
    /// Use `start_noncontinuous_frame!` instead.
    ///
    /// `name` must contain a NULL byte.
    #[doc(hidden)]
    pub unsafe fn start_noncontinuous_frame(name: &'static str) -> Frame {
        #[cfg(feature = "enable")]
        {
            sys::___tracy_emit_frame_mark_start(name.as_ptr() as _);
        }
        Self(name)
    }
}

impl Drop for Frame {
    fn drop(&mut self) {
        #[cfg(feature = "enable")]
        unsafe {
            sys::___tracy_emit_frame_mark_end(self.0.as_ptr() as _);
        }
    }
}

/// Output a message.
///
/// `callstack_depth` specifies the maximum number of stack frames client should collect.
pub fn message(message: &str, callstack_depth: u16) {
    #[cfg(feature = "enable")]
    unsafe {
        sys::___tracy_emit_message(
            message.as_ptr() as _,
            message.len(),
            adjust_stack_depth(callstack_depth).into(),
        )
    }
}

/// Output a message with an associated color.
///
/// `callstack_depth` specifies the maximum number of stack frames client should collect.
///
/// The colour shall be provided as RGBA, where the least significant 8 bits represent the alpha
/// component and most significant 8 bits represent the red component.
pub fn color_message(message: &str, rgba: u32, callstack_depth: u16) {
    #[cfg(feature = "enable")]
    unsafe {
        sys::___tracy_emit_messageC(
            message.as_ptr() as _,
            message.len(),
            rgba >> 8,
            adjust_stack_depth(callstack_depth).into(),
        )
    }
}

/// Set the current thread name to the provided value.
pub fn set_thread_name(name: &str) {
    #[cfg(feature = "enable")]
    unsafe {
        let name = CString::new(name).unwrap();
        // SAFE: `name` is a valid null-terminated string.
        sys::___tracy_set_thread_name(name.as_ptr() as _)
    }
}

/// Create an instance of plot that can plot arbitrary `f64` values.
///
/// # Examples
///
/// ```
/// # use tracy_client::*;
/// enable();
/// static TEMPERATURE: Plot = create_plot!("temperature");
/// TEMPERATURE.point(37.0);
/// ```
#[macro_export]
macro_rules! create_plot {
    ($name: expr) => {
        unsafe { $crate::Plot::new_unchecked(concat!($name, "\0")) }
    };
}

/// A plot for plotting arbitary `f64` values.
///
/// Create with the [`create_plot`](create_plot) macro.
pub struct Plot(&'static str);

impl Plot {
    /// Use `create_plot!` instead.
    #[doc(hidden)]
    pub const unsafe fn new_unchecked(name: &'static str) -> Self {
        Self(name)
    }

    /// Add a point with `y`-axis value of `value` to the plot.
    pub fn point(&self, value: f64) {
        #[cfg(feature = "enable")]
        unsafe {
            sys::___tracy_emit_plot(self.0.as_ptr() as _, value);
        }
    }
}

/// Adjust the stack depth to maximum supported by tracy.
#[inline(always)]
#[cfg(windows)]
const fn adjust_stack_depth(depth: u16) -> u16 {
    62 ^ ((depth ^ 62) & 0u16.wrapping_sub((depth < 62) as _))
}

/// Adjust the stack depth to maximum supported by tracy.
#[inline(always)]
#[cfg(not(windows))]
const fn adjust_stack_depth(depth: u16) -> u16 {
    depth
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn zone_values() {
        enable();
        let span = Span::new("test zone values", "zone_values", file!(), line!(), 100);
        span.emit_value(42);
        span.emit_text("some text");
    }

    #[test]
    fn finish_frameset() {
        enable();
        for _ in 0..10 {
            finish_continuous_frame!();
        }
    }

    #[test]
    fn finish_secondary_frameset() {
        enable();
        for _ in 0..5 {
            finish_continuous_frame!("every two seconds");
        }
    }

    #[test]
    fn non_continuous_frameset() {
        enable();
        let _: Frame = start_noncontinuous_frame!("weird frameset");
    }

    #[test]
    fn plot_something() {
        enable();
        static PLOT: Plot = create_plot!("a plot");
        for i in 0..10 {
            PLOT.point(i as f64);
        }
    }

    #[test]
    fn span_macro() {
        enable();
        let span = span!("macro span", 42);
        span.emit_value(42);
        let span = span!("macro span");
        span.emit_value(62);
    }
}
