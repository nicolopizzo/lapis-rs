#[macro_export]
macro_rules! debug {
    ( $fun: expr ) => {{
        info!(target: "FOLDING", "{{{{{{");
        unsafe { OPEN_DEBUG += 1 }
        let res = $fun;
        unsafe { OPEN_DEBUG -= 1 }
        info!(target: "FOLDING", "}}}}}}");
        res
    }};
}
