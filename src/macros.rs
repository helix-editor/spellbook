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
