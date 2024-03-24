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

// This is basically `flag.is_some_and(|flag| flags.contains(&flag))` but less verbose.
// This is necessary because we represent a lot of flags on `AffOptions` as `Option<NonZeroU16>`.
// TODO: forget about `Option<NonZeroU16>` and just use the zero u16? Measure performance change.
#[macro_export]
macro_rules! has_flag {
    ( $flags:expr, $flag:expr ) => {{
        match $flag {
            Some(flag) => $flags.contains(&flag),
            None => false,
        }
    }};
}
