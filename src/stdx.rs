// A port of Rust 1.70.0's `Option::is_some_and` so we can keep the MSRV low.
pub fn is_some_and<T>(option: Option<T>, f: impl FnOnce(T) -> bool) -> bool {
    match option {
        None => false,
        Some(x) => f(x),
    }
}
