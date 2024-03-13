#[macro_export]
macro_rules! flag {
    ( $x:expr ) => {{
        Flag::new($x).unwrap()
    }};
}

#[macro_export]
macro_rules! flagset {
    ( $( $x:expr ),* ) => {
        {
            FlagSet::from_iter( [ $( Flag::new( $x ).unwrap() ),* ].into_iter() )
        }
    }
}
