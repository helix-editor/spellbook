// Convenience macros for initializing flags and flagsets. Mostly used by the unit tests.
#[macro_export]
macro_rules! flag {
    ( $x:expr ) => {{
        Flag::new($x as u16).unwrap()
    }};
}
#[macro_export]
macro_rules! flagset {
    () => {{
        FlagSet::empty()
    }};
    ( $( $x:expr ),* ) => {
        {
            FlagSet::from( $crate::alloc::vec![ $( Flag::new( $x as u16 ).unwrap() ),* ] )
        }
    };
}

// This is `flag.is_some_and(|flag| flags.contains(&flag))` but less verbose.
// This is useful because we represent a lot of flags on `AffOptions` as `Option<NonZeroU16>`.
// TODO: forget about `Option<NonZeroU16>` and just use the zero u16? Measure performance change.
// TODO: forget the macro and use `is_some_and`? The MSRV is now high enough that it's acceptable.
#[macro_export]
macro_rules! has_flag {
    ( $flags:expr, $flag:expr ) => {{
        match $flag {
            Some(flag) => $flags.contains(&flag),
            None => false,
        }
    }};
}
