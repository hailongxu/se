use crate::{push_frame, CondStack, FnCodeMap, FrameVec,};
use crate::types::{Exit,RetRule,Data};
use crate::token::{Bracket,Fndef};
use crate::ast::{Auxi, Bound, CorreE, Ifflow, LeadBound, Whileflow};
use crate::pop::{
    Opi, Para, PopSubjectMatter, 
    do_if_else, do_if_then, do_while_body
};


pub(crate) fn push_exp<'a>(corre:CorreE, corre_size: usize,frame_stack: &mut FrameVec, cond_stack: &'a mut CondStack)->PopSubjectMatter<'a> {
    match cond_stack.last() {
        Some(FlowBool::If(ifstate,stacksize)) => {
            match ifstate {
                IfState::If0|IfState::ThenDo|IfState::ElseDo
                    => {}
                IfState::ThenDone => {
                    if corre_size < *stacksize {
                        debug_assert_eq!(corre_size+1,*stacksize);
                        debug_assert!(matches!(corre,CorreE::Ifc(Ifflow::End)));
                        cond_stack.pop();
                        return PopSubjectMatter::Pr(Ifflow::END_PRINUM,RetRule::Ignore);
                    }
                    return PopSubjectMatter::Donot;
                }
                IfState::ThenDonot => {
                    match corre_size.cmp(stacksize) {
                        std::cmp::Ordering::Less => {
                            debug_assert!(corre_size+1==*stacksize);
                            debug_assert!(matches!(corre,CorreE::Ifc(Ifflow::End)));
                            cond_stack.pop();
                            return PopSubjectMatter::Pr(Ifflow::END_PRINUM, RetRule::Ignore);
                        }
                        std::cmp::Ordering::Equal => {
                            match corre {
                                CorreE::Ifc(Ifflow::Else) => {
                                    cond_stack.update_if(IfState::ElseDo);
                                }
                                CorreE::Ifc(Ifflow::Elif) => {
                                    cond_stack.update_if(IfState::If0);
                                }
                                _=>{}
                            }
                        }
                        std::cmp::Ordering::Greater => {}
                    }
                    return PopSubjectMatter::Donot;
                }
                IfState::ElseDonot => {
                    match corre_size.cmp(stacksize) {
                        std::cmp::Ordering::Less => {
                            debug_assert!(corre_size+1==*stacksize);
                            debug_assert!(matches!(corre,CorreE::Ifc(Ifflow::End)));
                            cond_stack.pop();
                            return PopSubjectMatter::Pr(Ifflow::END_PRINUM, RetRule::Ignore);
                        }
                        std::cmp::Ordering::Equal |
                        std::cmp::Ordering::Greater => {}
                    }
                    return  PopSubjectMatter::Donot;
                }
                // IfState::ElseDone => {}
            }
        }
        Some(FlowBool::While(whilestate, stacksize, _offset)) => {
            match whilestate {
                WhileState::While1 => {debug_assert!(true,"do next");}
                WhileState::BodyDo => {debug_assert!(true,"do next");}
                WhileState::ElseDo => {debug_assert!(true,"do next");}
                WhileState::BodyDonot => {
                    match corre_size.cmp(stacksize) {
                        std::cmp::Ordering::Less => {
                            debug_assert!(corre_size+1==*stacksize);
                            debug_assert!(matches!(corre,
                                CorreE::Whc(Whileflow::Body(Bound::End))|
                                CorreE::Whc(Whileflow::Else(LeadBound::End))
                            ));
                            cond_stack.pop();
                            return PopSubjectMatter::Pr(Whileflow::WHILE_END_PRINUM, RetRule::Ignore);
                        }
                        std::cmp::Ordering::Equal => {
                            match corre {
                                CorreE::Whc(Whileflow::Body(Bound::End)) |
                                CorreE::Whc(Whileflow::Else(LeadBound::Head)) =>
                                    return PopSubjectMatter::Donot,
                                CorreE::Whc(Whileflow::Else(LeadBound::Begin)) => {
                                    cond_stack.update_while(WhileState::ElseDo);
                                    return PopSubjectMatter::Donot;
                                }
                                _=> return PopSubjectMatter::Donot,
                            }
                        }
                        std::cmp::Ordering::Greater => {
                            return PopSubjectMatter::Donot;
                        }
                    }
                }
                WhileState::BreakDone => {
                    if corre_size < *stacksize {
                        // While-End
                        debug_assert!(corre_size+1==*stacksize);
                        debug_assert!(matches!(corre,
                            CorreE::Whc(Whileflow::Body(Bound::End))|
                            CorreE::Whc(Whileflow::Else(LeadBound::End))
                        ));
                        cond_stack.pop();
                        return PopSubjectMatter::Pr(Whileflow::WHILE_END_PRINUM, RetRule::Ignore);
                    } else {
                        return PopSubjectMatter::Donot;
                    }
                }
            }
        }
        None => {}
    }

    println!("\tdown-todo ---> ...");
    match corre {
        CorreE::Fnast(_) => unreachable!("should be done in ast part"),
        CorreE::Ifc(Ifflow::If(stacksize)) => {
            //1
            let _ = push_frame(frame_stack);
            cond_stack.push(FlowBool::If(IfState::If0,stacksize));
            // PopSubjectMatter::Pr(Ifflow::BEGIN_PRINUM, RetRule::Ignore)
            PopSubjectMatter::Donot
        }
        CorreE::Ifc(Ifflow::Then) => {
            //1
            debug_assert!(matches!(cond_stack.last(),Some(FlowBool::If(IfState::If0,_))));
            let Some(flowbool) = cond_stack.last_mut() else {
                unreachable!("internal error");
            };
            PopSubjectMatter::PrCond(Ifflow::INNER_PRINUM,RetRule::Ignore,do_if_then,flowbool)
        }
        CorreE::Ifc(Ifflow::Ifelse) => {
            debug_assert!(matches!(cond_stack.last(),Some(FlowBool::If(IfState::If0,_))));
            let Some(flowbool) = cond_stack.last_mut() else {
                unreachable!("internal error");
            };
            PopSubjectMatter::PrCond(Ifflow::INNER_PRINUM,RetRule::Ignore,do_if_else,flowbool)
        }
        CorreE::Ifc(Ifflow::Else) => {
            //1
            debug_assert!(matches!(cond_stack.last_mut(),Some(FlowBool::If(IfState::ThenDo,_))));
            cond_stack.update_if(IfState::ThenDone);
            PopSubjectMatter::Pr(Ifflow::INNER_PRINUM,RetRule::Ignore)
        }
        CorreE::Ifc(Ifflow::Elif) => {
            //1
            debug_assert!(matches!(cond_stack.last_mut(),Some(FlowBool::If(IfState::ThenDo,_))));
            cond_stack.update_if(IfState::ThenDone);
            PopSubjectMatter::Pr(Ifflow::INNER_PRINUM,RetRule::Ignore)
        }
        CorreE::Ifc(Ifflow::End) => {
            //1
            debug_assert!(matches!(cond_stack.last_mut(),Some(FlowBool::If(IfState::ThenDo|IfState::ElseDo,_))));
            cond_stack.update_if(IfState::ThenDone);
            // cond_stack.update_if(IfState::ElseDone);
            cond_stack.pop(); // the cond of if is done
            PopSubjectMatter::Pr(Ifflow::END_PRINUM, RetRule::Ignore)
        }

        // while running structure
        CorreE::Whc(Whileflow::While(stacksize,offset)) => {
            let _ = push_frame(frame_stack);
            cond_stack.push(FlowBool::While(WhileState::While1,stacksize,offset));
            // PopSubjectMatter::Pr(Whileflow::WHILE_BEGIN_PRINUM, RetRule::Ignore)
            PopSubjectMatter::Donot
        }
        CorreE::Whc(Whileflow::Body(Bound::Begin)) => {
            let flowbool = cond_stack.last_mut().unwrap();
            debug_assert!(matches!(flowbool,FlowBool::While(WhileState::While1,..)));
            PopSubjectMatter::PrCond(Whileflow::BODY_BEGIN_PRINUM,RetRule::Ignore,do_while_body,flowbool)
        }
        CorreE::Whc(Whileflow::Body(Bound::End)) => {
            debug_assert!({
                let Some(FlowBool::While(WhileState::BodyDo,stacksize,_offset)) = cond_stack.last() else {
                    unreachable!("grammer error");
                };
                corre_size == *stacksize || corre_size+1 == *stacksize
            });
            cond_stack.update_while(WhileState::While1);
            let Some(FlowBool::While(..,stacksize,offset)) = cond_stack.last() else {
                unreachable!("never will be happen here");
            };
            PopSubjectMatter::PrAgain(Whileflow::BODY_END_PRINUM,RetRule::Ignore,*stacksize,*offset)
        }
        CorreE::Whc(Whileflow::Continue) => {
            match cond_stack.last().unwrap() {
                FlowBool::While(WhileState::BodyDo,stacksize,offset) => {
                    let stacksize = *stacksize;
                    let offset = *offset;
                    cond_stack.update_while(WhileState::While1);
                    PopSubjectMatter::PrAgain(Whileflow::BODY_END_PRINUM,RetRule::Ignore,stacksize,offset)
                }
                FlowBool::If(IfState::ThenDo|IfState::ElseDo,_) => {
                    while let Some(FlowBool::If(ifstate,_)) = cond_stack.last() {
                        debug_assert!(matches!(ifstate,IfState::ThenDo|IfState::ElseDo));
                        cond_stack.pop();
                    }
                    let Some(FlowBool::While(WhileState::BodyDo,stacksize,offset)) = cond_stack.last() else {
                        unreachable!("never reach here");
                    };
                    let stacksize = *stacksize;
                    let offset = *offset;
                    cond_stack.update_while(WhileState::While1);
                    PopSubjectMatter::PrAgain(Whileflow::BODY_END_PRINUM,RetRule::Ignore,stacksize,offset)
                }
                _=> unimplemented!("grammer error")
            }
        }
        CorreE::Whc(Whileflow::Break(LeadBound::Head|LeadBound::Begin)) => {
            PopSubjectMatter::Pr(Whileflow::BREAK_BEGIN_PRINUM, RetRule::Ignore)
        }
        CorreE::Whc(Whileflow::Break(LeadBound::End)) => {
            match cond_stack.last().unwrap() {
                FlowBool::While(WhileState::BodyDo|WhileState::ElseDo,..) => {
                    cond_stack.update_while(WhileState::BreakDone);
                    PopSubjectMatter::Donot
                }
                FlowBool::If(IfState::ThenDo|IfState::ElseDo,_) => {
                    while let Some(FlowBool::If(ifstate,_)) = cond_stack.last() {
                        debug_assert!(matches!(ifstate,IfState::ThenDo|IfState::ElseDo));
                        cond_stack.pop();
                    }
                    debug_assert!(matches!(cond_stack.last(),
                        Some(FlowBool::While(WhileState::BodyDo|WhileState::ElseDo,..))));
                    PopSubjectMatter::Donot // do the action when meet the while-end
                }
                _=> unreachable!("the program internal error")
            }
        }
        CorreE::Whc(Whileflow::Else(LeadBound::Head|LeadBound::Begin)) => {
            unreachable!("should be done in ast procedure or in Donot part of current func");
        }
        CorreE::Whc(Whileflow::Else(LeadBound::End)) => {
            debug_assert!({
                let Some(FlowBool::While(WhileState::ElseDo, stacksize, _offset)) = cond_stack.last() else {
                    panic!("program internal error");
                };
                corre_size+1 == *stacksize
            });
            cond_stack.pop();
            PopSubjectMatter::Pr(Whileflow::WHILE_END_PRINUM, RetRule::Ignore)
        }

        CorreE::Sub(Bracket::RRound) => {
            PopSubjectMatter::Pr(Bracket::RRound.prinum(),RetRule::Ignore)
        }
        CorreE::Sub(Bracket::LRound) => {
            push_frame(frame_stack);
            PopSubjectMatter::Donot
        }
        CorreE::Aux(aux) => {
            let info: &Auxi = aux.info();
            PopSubjectMatter::Pr(info.prinum,info.retrule)
        }
        // CorreE::Comma => {
        //     PopSubjectMatter::Pr(PriNum::P1,RetRule::Ignore)
        // }
        // CorreE::End(End) => {
        //     PopSubjectMatter::Pr(End::PRINUM, RetRule::Ignore)
        // }
        CorreE::Data(data) => {
            push_data(data, &mut frame_stack.last_mut().unwrap().data);
            PopSubjectMatter::Donot
        },
        CorreE::Op(op, para) => {
            let frame = frame_stack.last_mut().unwrap();
            if frame.opi.last().is_none() || frame.opi.last().unwrap().0.prinum < op.prinum {
                push_action((op,para), &mut frame_stack.last_mut().unwrap().opi);
                PopSubjectMatter::Donot
            } else {
                // pass to pop procedure
                PopSubjectMatter::Op(op, para)
            }
        },
        // CorreE::AstsrcRelocate(_) => {
        //     assert!(false, "should be done with before the funtion call");
        //     PopSubjectMatter::Donot
        // }
        CorreE::IgnoreNextSteps => {
            assert!(false, "we should deal with condition after ast function");
            PopSubjectMatter::Donot
        }
        CorreE::Exit(Exit) => {
            PopSubjectMatter::Pr(Exit::PRINUM, RetRule::Ignore)
        }
    }
}


/// while state machine
/// which control the flow of while loop flow run as its design
/// this value is not belonged to user-code just inner state
/// includes all kinds of flags such while body continue break else etc..
#[derive(Debug)]
pub(crate) enum WhileState {
    // Cond(bool),
    While1,
    BodyDo,
    BreakDone,
    BodyDonot,
    ElseDo,
    // End,
    // True,
    // False,
    // Break,
    // Else,
}
/// if state machine
/// which control the flow of if branch flow run as its design
/// this value is not belonged to user-code just inner state
/// includes all kinds of flags such if then else etc..
#[derive(Debug)]
pub(crate) enum IfState {
    If0,
    ThenDo,ThenDone,ThenDonot,
    ElseDo,/*ElseDone,*/ElseDonot,
    /*End,*/
}
#[derive(Debug)]
pub(crate) enum FlowBool {
    // while-state, stack-size, offset
    While(WhileState,usize,usize),
    // if-state, stack-size
    If(IfState,usize),
}


// if I clear all but keep the last, added here

fn push_data(v:Data, stack: &mut Vec<Data>) {
    println!("\t++++ push data {v:?}");
    stack.push(v);
}
fn push_action(opi:(Opi,Para), stack: &mut Vec<(Opi,Para)>) {
    println!("\t++++ push op {:?} {:?}",opi.0.name,opi.1);
    stack.push(opi);
}
pub(crate) fn push_fndef(fndef:Fndef, codes:&mut FnCodeMap) {
    println!("\t++++ push fn {:?}", fndef);
    codes.insert(fndef.name.clone(), fndef);
}
