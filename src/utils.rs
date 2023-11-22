use std::rc::Rc;

use crate::lnode::LNode;

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


    ( $fun: expr, $target: expr ) => {{
        info!(target: $target, "{{{{{{");
        unsafe { OPEN_DEBUG += 1 }
        let res = $fun;
        unsafe { OPEN_DEBUG -= 1 }
        info!(target: $target, "}}}}}}");
        res
    }};
}

pub fn get_head(term: &Rc<LNode>) -> &Rc<LNode> {
    match &**term {
        LNode::App { left, .. } => get_head(left),
        _ => term,
    }
}
