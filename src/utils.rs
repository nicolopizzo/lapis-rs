#[macro_export]
macro_rules! debug {
    ( $fun: expr ) => {{
        info!("{{");
        unsafe { OPEN_DEBUG += 1 }
        let res = $fun;
        unsafe { OPEN_DEBUG -= 1 }
        info!("}}");
        res
    }};
}
