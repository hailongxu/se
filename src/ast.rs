use crate::{CorrespondVec, FnCodeMap,};
use crate::types::{Data, Keyword, PriNum, Exit, RetRule};
use crate::token::{test_next_token_else, Bracket, Curly, Fndef, Token};
use crate::push::push_fndef;
use crate::pop::{Opi, Para,};


// struct SrcNext(bool);
pub(crate) fn ast_correspond(token:Token, whole:&[char], src:&[char], correspond:&mut CorrespondVec, codes:&mut FnCodeMap)->Option<CorreE> {
    // match correspond.last() {
    //     Some(CorreE::Whc(Whileflow::Body(Bound::End))) => {
    //         if let Token::Kw(Keyword::Else) = token {
    //             correspond.update(CorreE::Whc(Whileflow::Else(LeadBound::Head)));
    //             return Some(CorreE::IgnoreNextSteps)
    //         // } else {
    //         //     // token backforward one ******, rest src do not assign to src, remind
    //         //     assert!(false,"xxxxxxxx");
    //         //     return Some(CorreE::Whc(Whileflow::End));
    //         }
    //     }
    //     _ => (),
    // }

    // if exp is at the first pos, we flag it
    let mut start_new_exp = false;

    let ce = match token {
        Token::Pr(Bracket::LRound) => {
            start_new_exp = true;
            correspond.push(CorreE::Sub(Bracket::LRound));
            CorreE::Sub(Bracket::LRound)
        }
        Token::Pr(Bracket::RRound) => {
            if let Some(CorreE::Sub(Bracket::LRound)) = correspond.last() {
                correspond.pop(CorreE::Sub(Bracket::RRound));
            } else {
                // Erorr return; for future
                panic!("the backert not corresponed");
            }
            CorreE::Sub(Bracket::RRound)
        }

        Token::Aux(Aux::Semicolon) => {
            start_new_exp = true;
            CorreE::Aux(Aux::Semicolon)
        } // ignore

        Token::Aux(Aux::Comma) => {
            start_new_exp = true;
            // let mut is_fndef_end = false; // not need anymore in 1.82
            match correspond.last() {
                // fn def complete
                Some(CorreE::Fnast(Fnast::Decl(name,ps,index))) => {
                    // is_fndef_end = true; // not need anymore in 1.82
                    // we can put an advice to rust 
                    // because the ref does not use after push
                    // correspond.push(CorreE::Fnast(Fnast::End));
                    let ps = ps.clone();
                    let body = &whole[whole.len()-index..whole.len()-src.len()];
                    let body = body.iter().map(|e|*e).collect::<Vec<char>>();
                    let fndef = Fndef {name:name.clone(), ps, body};
                    push_fndef(fndef,codes);
                    // OMG, it works well in Ver.1.82, while that can not pass the grammer check in Ver.1.81
                    // the iteration speed is quit good
                    correspond.pop(CorreE::Aux(Aux::Comma));
                    correspond.pop_fndef();
                    CorreE::IgnoreNextSteps
                }
                Some(CorreE::Whc(Whileflow::Break(LeadBound::Begin))) => {
                    correspond.pop(CorreE::Whc(Whileflow::Break(LeadBound::End)));
                    // convert to While-break-end
                    // CorreE::Whc(Whileflow::Break(LeadBound::End))
                    // we calculate the final action until we run across the while-end
                    // correspond.set_fndef(true);
                    CorreE::Whc(Whileflow::Break(LeadBound::End))
                }
                _ => CorreE::Aux(Aux::Comma) // ignore
            }
            // and this code can be moved into the case of CorreE::Fnast position
            // if is_fndef_end {
            //     correspond.pop(CorreE::Aux(Aux::Comma));
            //     correspond.pop_verify();
            // } else {
            //     CorreE::Aux(Aux::Comma)
            // }
        }

        Token::Fndecl(name,ps) => {
            start_new_exp = true;
            correspond.push(CorreE::Fnast(Fnast::Decl(name, ps, src.len())));
            correspond.push_fndef();
            CorreE::IgnoreNextSteps
        }

        Token::Kw(Keyword::If) => {
            start_new_exp = true;
            let stacksize = correspond.len()+1;
            correspond.push(CorreE::Ifc(Ifflow::If(stacksize)));
            // correspond.push_fndef(correspond.is_fndef());
            // correspond.push_condition(false);
            debug_assert_eq!(stacksize,correspond.len());
            CorreE::Ifc(Ifflow::If(stacksize)) // we start a sub, use this
        }
        Token::Kw(Keyword::Then) => {
            start_new_exp = true;
            match correspond.last() {
                Some(CorreE::Ifc(Ifflow::If(_)|Ifflow::Elif)) => {
                    correspond.update(CorreE::Ifc(Ifflow::Then));
                    CorreE::Ifc(Ifflow::Then)
                }
                _ => panic!("the script is not obeyed by rules"),
            }
        }
        Token::Kw(Keyword::Elif) => {
            start_new_exp = true;
            if let Some(CorreE::Ifc(Ifflow::Then)) = correspond.last() {
                correspond.update(CorreE::Ifc(Ifflow::Elif));
                // correspond.set_fndef(correspond.was_true());
                CorreE::Ifc(Ifflow::Elif)
            } else {
                panic!("the script is not obeyed by rules");
            }
        }
        Token::Kw(Keyword::Else) => {
            start_new_exp = true;
            match correspond.last() {
                Some(CorreE::Ifc(Ifflow::Then)) => {
                    correspond.update(CorreE::Ifc(Ifflow::Else));
                    // if correspond.is_running() || correspond.was_true() {
                    //     correspond.set_fndef(true);
                    //     CorreE::IgnoreNextSteps
                    // } else {
                    //     correspond.set_fndef(false);
                    //     debug_assert!(correspond.is_running());
                    //     CorreE::IgnoreNextSteps
                    // }
                    CorreE::Ifc(Ifflow::Else)
                }
                Some(CorreE::Ifc(Ifflow::If(_)|Ifflow::Elif)) => {
                    correspond.update(CorreE::Ifc(Ifflow::Else));
                    CorreE::Ifc(Ifflow::Ifelse)
                }
                Some(CorreE::Whc(Whileflow::Body(Bound::End))) => {
                    correspond.update(CorreE::Whc(Whileflow::Else(LeadBound::Head)));
                    CorreE::IgnoreNextSteps
                }
                _ => panic!("the if-then-elif grammer error"),
            }
        }
        Token::Kw(Keyword::End) => {
            match correspond.last() {
                Some(CorreE::Ifc(Ifflow::Then|Ifflow::Else|Ifflow::Elif)) => {
                    correspond.pop(CorreE::Ifc(Ifflow::End));
                    // correspond.pop_fndef();
                    // correspond.pop_condition();
                }
                _ => panic!("the if-then-elif grammer error"),
            }
            // at present end is just used for if-then statement
            CorreE::Ifc(Ifflow::End)
        }

        Token::Kw(Keyword::While) => {
            start_new_exp = true;
            let stacksize = correspond.len()+1;
            let offset = whole.len()-src.len();
            let whilehead = Whileflow::While(stacksize,offset);
            correspond.push(CorreE::Whc(whilehead));
            debug_assert_eq!(stacksize,correspond.len());
            // correspond.push_offset(whole.len()-src.len());
            // correspond.push_fndef(correspond.is_fndef());
            // correspond.push_condition(false);
            CorreE::Whc(whilehead)
        }
        Token::Curly(Curly::LCurly) => {
            start_new_exp = true;
            match correspond.last() {
                Some(CorreE::Whc(Whileflow::While(..))) => {
                    correspond.update(CorreE::Whc(Whileflow::Body(Bound::Begin)));
                    CorreE::Whc(Whileflow::Body(Bound::Begin))
                }
                Some(CorreE::Whc(Whileflow::Body(Bound::End))) => {
                    correspond.update(CorreE::Whc(Whileflow::Body(Bound::Begin)));
                    CorreE::Whc(Whileflow::Body(Bound::Begin))
                }
                Some(CorreE::Whc(Whileflow::Else(LeadBound::Head))) => {
                    correspond.update(CorreE::Whc(Whileflow::Else(LeadBound::Begin)));
                    // correspond.set_fndef(correspond.was_true());
                    CorreE::Whc(Whileflow::Else(LeadBound::Begin))
                }
                other => panic!("the script is not obeyed by rules: {:?}",other),
            }
        }
        Token::Kw(Keyword::Continue) => {
            start_new_exp = true;
            match correspond.last() {
                Some(CorreE::Whc(Whileflow::Body(Bound::Begin))) => {
                    // correspond.pop(CorreE::Whc(Whileflow::Body(Bound::End)));
                    // let Some(CorreE::Whc(Whileflow::While(offset))) = correspond.last().cloned() else {
                    //     unreachable!("grammer error or jit error");
                    // };
                    // // correspond.set_fndef(correspond.was_true());
                    // // restore the src to while begin
                    // debug_assert!(correspond.relocate_offset.is_none());
                    // let _ = correspond.relocate_offset.insert(offset);
                    CorreE::Whc(Whileflow::Continue)
                }
                Some(CorreE::Ifc(Ifflow::Then|Ifflow::Ifelse|Ifflow::Else)) => {
                    CorreE::Whc(Whileflow::Continue)
                }
                _ => panic!("the script is not obeyed by rules"),
            }
        }
        Token::Kw(Keyword::Break) => {
            start_new_exp = true;
            match correspond.last() {
                Some(CorreE::Whc(Whileflow::Body(Bound::Begin)|Whileflow::Else(LeadBound::Begin))) => {
                    correspond.push(CorreE::Whc(Whileflow::Break(LeadBound::Begin)));
                    CorreE::Whc(Whileflow::Break(LeadBound::Begin))
                }
                Some(CorreE::Ifc(Ifflow::Then|Ifflow::Ifelse|Ifflow::Else)) => {
                    correspond.push(CorreE::Whc(Whileflow::Break(LeadBound::Begin)));
                    CorreE::Whc(Whileflow::Break(LeadBound::Begin))
                }
                _ => panic!("the script is not obeyed by rules"),
            }

            // match correspond.last() {
            //     Some(CorreE::Whc(Whileflow::Body(Bound::Begin))) => {
            //         correspond.push(CorreE::Whc(Whileflow::Break(LeadBound::Begin)));
            //         CorreE::IgnoreNextSteps
            //     }
            //     _ => panic!("the script is not obeyed by rules"),
            // }
        }
        Token::Curly(Curly::RCurly) => {
            match correspond.last() {
                Some(CorreE::Whc(Whileflow::Body(Bound::Begin))) => {
                    // correspond.update(CorreE::Whc(Whileflow::Body(Bound::End)));
                    // if correspond.is_running() {
                    //     let CorreE::Whc(Whileflow::While(offset)) =
                    //         correspond.update_and_prev(CorreE::Whc(Whileflow::Body(Bound::End))) else {
                    //         unreachable!("grammer error or jit error");
                    //     };
                    //     // restore the src to while begin
                    //     let offset = *offset;
                    //     let _ = correspond.relocate_offset.insert(offset);
                    //     CorreE::Whc(Whileflow::Body(Bound::End))
                    // } else
                    if let (true, _src_next) = test_next_token_else(src) {
                        correspond.update(CorreE::Whc(Whileflow::Body(Bound::End)));
                        // correspond.pop_fndef();
                        // correspond.pop_condition();
                        CorreE::Whc(Whileflow::Body(Bound::End)) // actually do nothing
                    } else {
                        correspond.pop(CorreE::Whc(Whileflow::Body(Bound::End)));
                        // should we use the result of test-next-token-else
                        // correspond.update(CorreE::Whc(Whileflow::Else(LeadBound::Head)));
                        CorreE::Whc(Whileflow::Body(Bound::End))
                    }
                }
                Some(CorreE::Whc(Whileflow::Else(LeadBound::Begin))) => {
                    correspond.pop(CorreE::Whc(Whileflow::Else(LeadBound::End)));
                    // correspond.update(CorreE::Whc(Whileflow::Else(LeadBound::End)));
                    // CorreE::Whc(Whileflow::Else(LeadBound::End)) // looks like the state is unnecessary
                    // correspond.pop(CorreE::Whc(Whileflow::End));
                    // correspond.pop_fndef();
                    // correspond.pop_condition();
                    CorreE::Whc(Whileflow::Else(LeadBound::End)) // do , and pop stack
                }
                _ => panic!("the script is not obeyed by rules"),
            }
        }

        Token::Kw(Keyword::Fn) => {CorreE::IgnoreNextSteps} // do nothing, this is processed in token parsing
        Token::Data(data) => {CorreE::Data(data)}, // for run todo
        Token::Op(op, para) => {CorreE::Op(op,para)}, // for run todo

        // Token::End(End) => {
        //     // do nothing at present, we can find another concise method to compose the if fn grammer
        //     CorreE::End(End)
        // }
        Token::Exit(Exit) => {
            CorreE::Exit(Exit)
        }

        // CorreE::Iffc(_) => unimplemented!("iff aaa, (bb*3);4, ccc+4, 支持这种简洁的形式，将来看看，目前先不支持，主要用于交互式计算，以简洁为主"),

        // CorreE::App(Bound::Begin) => {
        //     correspond.push(CorreE::App(Bound::Begin));
        //     unimplemented!();
        // }
        // CorreE::App(Bound::End) => {
        //     if let Some(CorreE::App(Bound::Begin)) = correspond.last() {
        //         correspond.pop().unwrap();
        //     } else {
        //         // Erorr return; for future
        //         panic!("the then not corresponed");
        //     };
        //     unimplemented!();
        // }
    };
    // println!("@@@ AST {:?}",correspond);
    correspond.exp_start = start_new_exp;
    if correspond.is_fndef() {
        Some(CorreE::IgnoreNextSteps)
    } else {
        Some(ce)
    }
}

// fn ast_src_relocate<'a>(corre_relocate:CorreE,whole:&'a[char],corre:CorreE)->Option<(&'a[char],CorreE)> {
//     if let CorreE::AstsrcRelocate(offset) = corre_relocate {
//         Some((&whole[offset..],corre))
//     } else {
//         None
//     }
// }


// #[derive(Clone, Copy)]
// enum Verify {
//     Literal,
//     Literaling(usize),
// }
#[derive(Clone,Debug)]
pub(crate) enum CorreE {
    // App(Bound),
    Fnast(Fnast),
    Sub(Bracket),
    Ifc(Ifflow),
    Whc(Whileflow),
    // Iffc(Iffflow),
    Aux(Aux),//SemiColon Comma,
    // End(End),
    Exit(Exit),
    // action part
    Data(Data),
    Op(Opi,Para),
    // above which does not need to be passed to push
    // AstsrcRelocate(usize),
    IgnoreNextSteps,
    // Lit(Verify),
}


#[derive(Clone,Debug)]
pub(crate) enum Sym {
    Str(&'static[char]),
    String(String),
}
impl Sym {
    fn as_char_slice(&self)->&'static[char] {
        let Sym::Str(s) = self else {
            panic!("not static char slice");
        };
        s
    }
    fn as_str(&self)->&str {
        let Sym::String(s) = self else {
            panic!("not static char slice");
        };
        s.as_str()
    }
    fn len(&self)->usize {
        match self {
            Sym::Str(s) => s.len(),
            Sym::String(s) => s.len(),
        }
    }
}


#[derive(Debug,Clone, Copy)]
pub(crate) enum Aux {
    Comma,
    Semicolon,
}
macro_rules! AuxComma {
    () => { ',' };
}
macro_rules! AuxSemiColon {
    () => { ';' };
}
#[derive(Clone, Copy)]
pub(crate) struct Auxi {
    pub(crate) id: Aux,
    name: char,
    pub(crate) prinum: PriNum,
    pub(crate) retrule: RetRule,
}

impl Aux {
    const METAS: [Auxi; 2] = [
        Aux::new(Aux::Comma,AuxComma!(),PriNum::P2,RetRule::Ignore),
        Aux::new(Aux::Semicolon,AuxSemiColon!(),PriNum::P2,RetRule::None),
    ];
    // const fn len() -> usize {
    //     Self::METAS.len()
    // }
    const fn new(id:Aux,name:char,prinum:PriNum,retrule:RetRule)->Auxi {
        Auxi {id,name,prinum,retrule}
    }
    const fn all()->&'static[Auxi] {
        &Self::METAS
    }
    const fn prinum(&self)->PriNum {
        self.info().prinum
    }
    const fn retrule(&self)->RetRule {
        self.info().retrule
    }
    pub(crate) const fn info(&self)->&'static Auxi {
        &Self::METAS[*self as usize]
    }
    pub(crate) /*const*/ fn match_starts(main:&[char])->(Option<&'static Auxi>,&[char]) {
        match main.first() {
            Some(AuxComma!()) => (Some(&Self::METAS[0]),&main[1..]),
            Some(AuxSemiColon!()) => (Some(&Self::METAS[1]),&main[1..]),
            _ => (None, main),
        }
    }
}




#[derive(Clone, Copy,Debug)]
pub(crate) enum Ifflow { If(usize)/*stacksize*/,Then,Elif,Ifelse,Else,End }
impl Ifflow {
    // if
    const BEGIN_PRINUM: PriNum = PriNum::P12;
    // then elif else
    pub(crate) const INNER_PRINUM: PriNum = PriNum::P2; 
    // end
    pub(crate) const END_PRINUM: PriNum = PriNum::P1; 
}
// #[derive(Clone, Copy)]
// enum Iffflow { Iff,Then,Else }


#[derive(Clone, Copy,Debug)]
pub(crate) enum LeadBound {
    Head,
    Begin,
    End,
}
#[derive(Clone,Copy,Debug)]
pub(crate) enum Whileflow { While(usize,usize)/*stacksize,offset */,Body(Bound),Continue,Break(LeadBound),Else(LeadBound)/*,End*/}
impl Whileflow {
    const WHILE_BEGIN_PRINUM: PriNum = PriNum::P12;
    pub(crate) const BODY_BEGIN_PRINUM: PriNum = PriNum::P2;
    pub(crate) const BODY_END_PRINUM: PriNum = PriNum::P2;
    pub(crate) const BREAK_BEGIN_PRINUM: PriNum = PriNum::P3;
    const BREAK_END_PRINUM: PriNum = PriNum::P2;
    pub(crate) const WHILE_END_PRINUM: PriNum = PriNum::P1;
}

#[derive(Clone, Copy,Debug)]
pub(crate) enum Bound {
    Begin,End,
}


#[derive(Clone,Debug)]
pub(crate) enum Fnast {
    Decl(String,Vec<String>,usize),
    End,
}
