use crate::{pop_frame, FrameVec, SymbolMap};
use crate::types::{Data, Et};



pub(crate) fn pop_frame_or_exit(frame_stack: &mut FrameVec,symbols:&SymbolMap)->Option<Option<Et>> {
    let Some(frame) = frame_stack.last() else {
        panic!("the flow would not run here");
        // return None; // the language ERR, now we just return None, future we will return Error Or panic
    };
    if /*cond.0 == PriNum::P0 &&*/ frame.opi.is_empty() {
        // assert_eq!(frame.data.len(),1);
        let vv = match frame.data.last() {
            // assure the value poped out must be val instead of sym
            // ******
            Some(Data::Sym(d)) => Some(symbols[d]),
            Some(Data::Val(d)) => Some(*d),
            None => None,
        };

        pop_frame(frame_stack);
        if let Some(last_frame) = frame_stack.last_mut() {
            if let Some(vv) = vv {
                last_frame.data.push(Data::Val(vv));
            } else {
                println!("***** nothing result with this frame");
            }
        } else {
            // no frame more and no op, so return
            println!("exit: trigger the exit value ~~~~~~");
            return Some(vv);
        }
    }
    None
}

