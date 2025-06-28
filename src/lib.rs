use std::collections::BTreeMap;


mod token;
mod types;

use token::{
    token_next,
    Token
};
use types::Data;
pub use types::Et;

use crate::ast::ast_correspond;
use crate::ast::Bound;
use crate::ast::Ifflow;
use crate::ast::Whileflow;
use crate::exit::pop_frame_or_exit;
use crate::pop::decide_todo;
use crate::pop::Opi;
use crate::pop::Para;
use crate::pop::PopSubjectMatter;
use crate::push::push_exp;
use crate::push::FlowBool;
use crate::push::IfState;
use crate::push::WhileState;
use crate::token::Bracket;
use crate::token::Fndef;


mod ast;
use ast::CorreE;

mod push;

mod pop;
mod exit;


fn parse_fn_exp(fn_def: Fndef, data:&[Et])->Option<Et> {
    let mut context = Context {
        frame_stack: Vec::<Frame>::new(),
        cond_stack: CondStack::new(),
        symbols: BTreeMap::new(),
        correspond: CorrespondVec::new(),
        fn_codes: BTreeMap::new(),
    };
    push_frame(&mut context.frame_stack);

    assert_eq!(data.len(), fn_def.ps.len(),"count of virtual params is not eq to count of real params");
    let src = fn_def.body.as_slice();

    // 把参数写入
    let pd_iter = data.iter().zip(fn_def.ps.iter());
    for (v,name) in pd_iter {
        context.symbols.insert(name.clone(),*v);
    }
    let vv = parse_exp(&mut context, src);
    vv
}
pub fn parse(src:&[char])->Option<Et> {
    let mut context = Context {
        frame_stack: Vec::<Frame>::new(),
        cond_stack: CondStack::new(),
        symbols: BTreeMap::new(),
        correspond: CorrespondVec::new(),
        fn_codes: BTreeMap::new(),
    };
    push_frame(&mut context.frame_stack);

    let vv = parse_exp(&mut context, src);
    vv
}


// next we will return Result<Option<Et>,Error>,
// if the exp does not have return value, return None, or return Et
// if some error happens, we return Error
// at preset, when error happens, we just panic the processing
fn parse_exp(context: &mut Context, src: &[char])->Option<Et> {
    let whole = src;
    let frame_stack = &mut context.frame_stack;
    // context.correspond.push_fndef(false);
    let cond_stack = &mut context.cond_stack;

    if src.is_empty() {
        return None;
    }

    // the char +/- is an sign of a number or an unique OP.
    // here, I think many ways to solve the problem.
    // At first, the new exp is just started by (, so, we can 
    //      let frame = frame_stack.last_mut().unwrap();
    //      let frame_empty = frame.data.is_empty() && frame.opi.is_empty();
    // use frame-empty as flag of exp stared, but this method is to be proofed that 
    // not all situation is covered. So the next,
    //
    // but now, we canot because situation is caused by many cases
    // I think some way to sovle:
    // 1, the SIGN shold be done by the token code only, which should not be helped
    //    by other parts. After thinking, It is not easy, and is not propriate, 
    //    because whether or not start a new exp is not deduced by token code context
    //    Strictly speaking, it is up to the grammer. so I abandon the way finally.
    // 2, for dependence of each code, So, under the complex situations, we set 
    //    the flag of new exp start in AST and stored in its struct. And assign 
    //    the flag at the main flow.

    let mut sign_number = true;
    let mut src = src;

    // println!("src: {src:?}", src=String::from_iter(src));
    // println!("@@@ AST {:?}",context.correspond);
    fn print_token_prompt(src:&[char],sign_number: bool) {
        println!("---------------------------------------------------");
        println!("Lexical : [{sign_number}] {}",String::from_iter(src));
    }
    fn print_token_result(token:&Token) {
        if let Token::Op(op,para) = &token {
            println!("\t=>token: {:?}", (&op.name,&op.act,para));
        } else {
            println!("\t=>token: {token:?}");
        };
    }
    fn print_corre_prompt() {
        print_prompt("corre");
    }
    fn print_corre_result(corre:&CorreE, correspond:&CorrespondVec) {
        println!("\t{:?}", correspond);
        if let CorreE::Op(Opi{name,..}, _)= corre {
            println!("\t=>corre: {:?}", name);
        } else {
            println!("\t=>corre: {:?}", corre);
        }
    }
    fn print_structure_prompt() {
        print_prompt("structure");
    }
    fn print_structure_result(subject_matter:&PopSubjectMatter,cond_stack:&CondStack,frame:&Frame) {
        println!("\tcontrol: {cond_stack:?}");
        println!("\tdata: {:?}",frame.data);
        println!("\top: [{}]",
            frame.opi.iter().fold(String::new(),
                |str,(op,para)|str+format!("{:?} ",(&op.name,&op.act,para)).as_str())
        );
        println!("\t=> structure: {subject_matter:?}");
    }
    fn print_action_prompt() {
        print_prompt("action");
    }
    fn print_prompt(prompt:&str) {
        println!("{prompt:.10}---")
    }

    let exit_value = loop {
        // let frame = frame_stack.last_mut().unwrap();
        // let frame_empty = frame.data.is_empty() && frame.opi.is_empty();
        print_token_prompt(src,sign_number);
        let Some((token, src_rest)) = token_next(src,sign_number,&context.fn_codes) else {
            return None; // error
        };
        print_token_result(&token);
        if sign_number {
            // here, if we get any token of data or op, means the position is not at the first, 
            // the +/- flag is RESET to false
            if let Token::Data(..)|Token::Op(..) = token {
                sign_number = false;
            }
        }
        print_corre_prompt();
        let Some(corre) = ast_correspond(token, whole, src_rest, &mut context.correspond, &mut context.fn_codes) else {
            return None; // error
        };
        print_corre_result(&corre,&context.correspond);
        if context.correspond.exp_start && !sign_number {
            sign_number = true;
        }
        src = src_rest;
        if let CorreE::IgnoreNextSteps = corre {
            continue;
        }
        let corre_size = context.correspond.len();
        let ptr = cond_stack as *const CondStack;
        print_structure_prompt();
        let subject_matter= push_exp(corre, corre_size, frame_stack, cond_stack);
        unsafe {
            // the only unsafe code here, just within the unsafe block, and has no harm to the code
            // and is absolutely safe totally. Please DONOT mind.
            let stack = std::mem::transmute::<*const CondStack, &CondStack>(ptr);
            print_structure_result(&subject_matter,stack,frame_stack.last_mut().unwrap());
        }
        if let PopSubjectMatter::Donot = subject_matter {
            continue;
        }
        let frame = frame_stack.last_mut().unwrap();
        // I want to move the code to the function of PrAgain(...,fn,)
        // but I havenot found an approviate way to do, becase the param passed is too many
        // and I donot to expand the size of PrAgain(..) type
        // Ok, looks like, Only I can do is reserved to solve it sometimes later
        if let PopSubjectMatter::PrAgain(_,_,stacksize,offset) = subject_matter {
            println!("<<<<<<<<<<<< src again back to: {offset}, stacksize: {stacksize}");
            src = src_again(whole, stacksize,offset,&mut context.correspond);
            if context.correspond.exp_start && !sign_number {
                sign_number = true;
            }
        }
        print_action_prompt();
        if let None = decide_todo(subject_matter, &context.fn_codes,&mut context.symbols,frame) {
            continue;
        }
        // if we return value from loop, the frame_stack will be called mut used 2 times
        if let Some(result) = pop_frame_or_exit(frame_stack, &context.symbols) {
            break result;
        }
    };
    // context.correspond.pop_fndef();
    debug_assert!(context.correspond.is_fndef_empty());

    exit_value
}

// fn ast_control_back(and_todo:AndTodo, correspond:&mut CorrespondVec)->Option<()> {
//     match and_todo {
//         AndTodo::Try => Some(()), // try to do pop_frame_or_exit
//         AndTodo::None => None,
//         AndTodo::ConditionBack(outside) => {
//             correspond.condition_back(outside);
//             None
//         }
//         AndTodo::BreakBack => {
//             correspond.break_end_back();
//             None
//         }
//     }
// }


// #[cfg(never)]
// fn parse_exp(context: &mut Context, src: &[char], just_grammer:bool)->Option<Et> {
//     let frame_stack = &mut context.frame_stack;

//     if src.is_empty() {
//         return None;
//     }
//     let mut src = src;

//     println!("src: {src:?}");
    
//     let rr = loop {
//         let mut frame = frame_stack.last_mut().unwrap();
//         let frame_empty = frame.data.is_empty() && frame.opi.is_empty();

//         let Some((ut, src_rest)) = token_next(src,frame_empty,&context.fn_codes) else {
//             // error
//             return None;
//         };

//         let r = match ut {
//             Token::Data(data) => {
//                 println!("++++>data: {:?} {:?}",data, src_rest);
//                 src = src_rest;
//                 if just_grammer {continue;}
//                 push_data(data, &mut frame.data);
//                 None
//             }

//             Token::Op(Opi { act: Act::Aux(tag), prinum,.. },..) => {
//                 println!("++++> op Aux ({:?}) {:?}",tag, src_rest);
//                 src = src_rest;
//                 let retrule = if let ";" = tag {RetRule::None} else {RetRule::Ignore};
//                 Some((prinum,retrule))
//             }

//             Token::Op(e,kind) => {
//                 if  frame.opi.last().is_none() ||
//                     frame.opi.last().unwrap().0.prinum < e.prinum
//                 {
//                     println!("++++> op : {:?} {:?}",e.name, src_rest);
//                     src = src_rest;
//                     if just_grammer { continue; }
//                     push_action((e.clone(),kind), &mut frame.opi);
//                     // 左目运算符，只和左边有关系，必须要执行
//                     // 这个和有无返回值没有关系啦，统一了，;也统一了
//                     // 本来是和左目和；运算符通用化的，后来；被辅助化以后或者说关键字话以后，基本就没用了
//                     // 除非有左目运算，要立即参与运算的，所以就返回了Some，要执行
//                     if let DataWhere::Left(_) = e.data_where {
//                         Some((e.prinum,RetRule::Ignore))
//                     } else {
//                         None
//                     }
//                 } else {
//                     Some((e.prinum,RetRule::Ignore))
//                 }
//             }

//             Token::Corr(CorreE::Sub(Bracket::LRound)) => {
//                 src = src_rest;
//                 println!("====> {:?}",src);
//                 if just_grammer {continue;}
//                 let frame_empty: Frame = Frame::new();
//                 frame_stack.push(frame_empty);
//                 frame = frame_stack.last_mut().unwrap();
//                 None
//             }

//             Token::Corr(CorreE::Sub(Bracket::RRound)) => {
//                 src = src_rest;
//                 println!("=====> ****** {src:?}");
//                 Some((PriNum::P0,RetRule::Ignore))
//             }

//             Token::Fndecl(fn_def) => {
//                 src = src_rest;
//                 println!("++++> CODE {:?} {:?}",fn_def, src_rest);
//                 if just_grammer {continue;}
//                 push_fndef(fn_def,&mut context.fn_codes);
//                 None
//             }

//             Token::Corr(CorreE::End) => {
//                 println!("==========> END {src:?}");
//                 Some((PriNum::P0,RetRule::Ignore))
//             }
//         };
//         if just_grammer {continue;}


//         // enum Bound {
//         //     Begin,
//         //     End
//         // }
//         // enum RunEle {
//         //     Data(Data),
//         //     Op(Opi),
//         //     Subexp(Bound),
//         // }
//         // fn exp_env(context:&mut Context,re:RunEle) {
//         //     fn top(context: &mut Context)->&mut Frame {
                
//         //     }
//         //     match re {
//         //         Data => {
//         //             push_data(Data::Val(et), &mut frame.data);
//         //         }
//         //     }
//         // }

//         if let Some(cond) = r {
//             try_pop_exp_util(&context.fn_codes,&mut context.symbols,frame, cond.clone());
//             if cond.0 == PriNum::P0 && frame.opi.is_empty() {
//                 // assert_eq!(frame.data.len(),1);
//                 let mut vv = frame.data.last().cloned();
//                 if let Some(Data::Sym(ref d)) = vv {
//                     // assure the value poped out must be val instead of sym
//                     // ******
//                     vv = Some(Data::Val(context.symbols[d]));
//                 }

//                 // let vv = value_of(&context.symbols, vv);
//                 frame_stack.pop();
//                 if let Some(last_frame) = frame_stack.last_mut() {
//                     if let Some(vv) = vv {
//                         last_frame.data.push(vv);
//                     } else {
//                         println!("***** nothing result with this frame");
//                     }
//                 } else {
//                     break vv;
//                 }
//             }
//         }
//     };

//     println!("return value = {rr:?}");
//     let Some(Data::Val(rr)) = rr else {
//         return None;
//     };
//     Some(rr)
// }




type SymbolMap = BTreeMap<String,Et>;
type FrameVec = Vec<Frame>;


// struct Hori(bool);
// impl Hori {
//     const PRINUM:PriNum = PriNum::P1;
//     const fn is_next_running(inside:bool, outside:bool)->bool{
//         !(inside ^ outside)
//     }
//     const fn is_next_verify(inside:bool, outside:bool)->bool{
//         inside ^ outside
//     }
//     // fn and_do(&self, outside: bool, frame_stack: &mut FrameVec) {
//     //     if Self::is_next_running(self.0, outside) {
//     //         push_frame(frame_stack);
//     //     }
//     // }
// } 
// const CORRESPOND_IF_UT: [(&[char], Token); 5] = [
//     (['i','f'].as_slice(),Token::Iff(Ifflow::If)),
//     (['t','h','e','n'].as_slice(),Token::Iff(Ifflow::Then)),
//     (['e','l','i','f'].as_slice(),Token::Iff(Ifflow::Elif)),
//     (['e','l','s','e'].as_slice(),Token::Iff(Ifflow::Else)),
//     (['e','n','d'].as_slice(),Token::End),
// ];
// impl ToChars for (&[char],Token) {
//     fn to_chars(&self)->&[char] {
//         self.0
//     }
// }

// end of sub programm
// #[derive(Debug,Clone, Copy)]
// struct End;
// impl End {
//     const PRINUM:PriNum = PriNum::P1;
// }



#[derive(Debug)]
struct Frame {
    // condition: Option<bool>,
    data: Vec<Data>,
    opi: Vec<(Opi,Para)>
}

impl Frame {
    fn new() -> Self {
        Self {/*condition:None,*/data:Vec::new(),opi:Vec::new()}
    }
}

// struct Unit<'a> {
//     ut: Token,
//     src_next: &'a[char],
// }

enum Indication {
    Data(Data),
    Op(Opi,Para),
    Sub(Bound),
    Pr(Bracket),
}


fn src_again<'a>(whole:&'a[char], stacksize:usize,offset:usize,correspond:&mut CorrespondVec)->&'a[char] {
    match correspond.len().cmp(&stacksize) {
        std::cmp::Ordering::Less =>
            correspond.push(CorreE::Whc(Whileflow::While(stacksize,offset))),
        std::cmp::Ordering::Equal =>
            correspond.update(CorreE::Whc(Whileflow::While(stacksize,offset))),
        std::cmp::Ordering::Greater => {
            loop {
                if let Some(CorreE::Whc(whileflow)) = correspond.last() {
                    debug_assert!(matches!(whileflow,Whileflow::Body(Bound::Begin)));
                    debug_assert_eq!(stacksize,correspond.len());
                    correspond.update(CorreE::Whc(Whileflow::While(stacksize,offset)));
                    break;
                }
                debug_assert!(matches!(correspond.last(),Some(CorreE::Ifc(Ifflow::Then|Ifflow::Else|Ifflow::Ifelse))));
                correspond.pop(CorreE::Whc(Whileflow::Continue));
            }
        }
    }
    correspond.exp_start = true;
    debug_assert_eq!(stacksize,correspond.len());
    &whole[offset..]
}

impl CorrespondVec {
    const fn new()->Self {
        Self {
            corre_stack: Vec::new(),
            fndef_stack: 0,
            exp_start: true,
            // offset_stack: Vec::new(),
            // condition_stack: Vec::new(),
            // relocate_offset: None,
        }
    }
    fn len(&self)-> usize {
        self.corre_stack.len()
    }
    fn last(&self)->Option<&CorreE> {
        self.corre_stack.last()
    }
    fn push(&mut self,corre:CorreE) {
        // println!("+++ AST: {corre:?}");
        self.corre_stack.push(corre);
    }
    fn pop(&mut self,cause:CorreE) {
        let v = self.corre_stack.pop();
        assert!(v.is_some());
        // println!("--- AST: {v:?} due to {cause:?}");
    }
    fn update(&mut self,corre:CorreE) {
        let Some(old) = self.corre_stack.last_mut() else {
            unreachable!("no items");
        };
        // println!("*** AST: {corre:?}  old: {:?}",*old);
        *old = corre;
    }
    // fn update_and_prev(&mut self,corre:CorreE)->&CorreE {
    //     let Some(old) = self.corre_stack.last_chunk_mut::<2>() else {
    //         unreachable!("no items");
    //     };
    //     println!("*** AST: {corre:?}  old: {:?}",*old);
    //     old[1] = corre;
    //     &old[0]
    // }
    const fn is_fndef_empty(&self)->bool {
        self.fndef_stack == 0
    }
    fn push_fndef(&mut self/* , verify:bool*/) {
        self.fndef_stack += 1;
        // let last = self.fndef_stack.last().unwrap_or(&(false,false)); 
        // self.fndef_stack.push((verify,last.0));
    }
    fn pop_fndef(&mut self) {
        // we should be sure the counter > 0
        // self.fndef_stack.pop().unwrap();
        debug_assert!(self.fndef_stack>0);
        self.fndef_stack -= 1;
    }
    // const fn exp_start(&self)->bool {
    //     self.exp_start
    // }
    // fn set_exp_start(&mut self) {
    //     self.exp_start = true;
    // }
    // fn push_offset(&mut self,offset:usize) {
    //     self.offset_stack.push(offset);
    // }
    // fn pop_offset(&mut self)->Option<usize> {
    //     self.offset_stack.pop()
    // }
    // fn last_offset(&self)->Option<&usize> {
    //     self.offset_stack.last()
    // }
    // fn set_fndef(&mut self, is_verified:bool) {
    //     let Some((verified,_)) = self.fndef_stack.last_mut() else {
    //         unreachable!("code should not be running here");
    //     };
    //     let old_verified = verified.clone();
    //     *verified = is_verified;
    //     println!("    AST ####### {} from {}  all{:?}",is_verified,old_verified,&self.fndef_stack);
    // }
    fn is_fndef(&self) -> bool {
        self.fndef_stack > 0
        // let Some(verify) = self.fndef_stack.last() else {
        //     unreachable!("code should not be running here");
        // };
        // verify.0 || verify.1
    }
    // fn is_running(&self) -> bool {
    //     !self.is_fndef()
    // }
    // fn is_true_todo(&self)->bool {
    //     match self.corre_stack.last().unwrap() {
    //         CorreE::Ifc(Ifflow::Then)|
    //         CorreE::Whc(Whileflow::Body(Bound::Begin)) => true,
    //         CorreE::Ifc(Ifflow::Else|Ifflow::Ifelse) => false,
    //         _ => unreachable!(),
    //     }
    // }
    // fn was_true(&self) -> bool {
    //     self.condition_stack.last().unwrap().clone()
    // }

    // fn 
    // // do_if(&mut self, predicate:bool), another define
    // fn todo_true_is_running(&mut self) {
    //     assert!(self.2.is_none());
    //     self.2 = Some(true);
    // }
    // fn todo_false_is_running(&mut self) {
    //     assert!(self.2.is_none());
    //     self.2 = Some(false);
    // }

    // const fn is_next_verify(inside:bool, outside:bool)->bool{
    //     inside ^ outside
    // }
    // fn push_condition(&mut self,cond:bool) {
    //     self.condition_stack.push(cond);
    // }
    // fn pop_condition(&mut self) {
    //     self.condition_stack.pop().unwrap();
    // }
    // fn condition(&self)->bool {
    //     self.condition_stack.last().unwrap().clone()
    // }
    // fn condition_back(&mut self, outside_cond:bool) {
    //     let inside = self.is_true_todo();
    //     let verified_new = Self::is_next_verify(inside,outside_cond);
    //     let condition_curr = self.condition();
    //     let Some((verified,_)) = self.fndef_stack.last_mut() else {
    //         unreachable!("code should not be running here");
    //     };
    //     println!("AST: condition:{} <-- {} verified:{} <-- {}",
    //         condition_curr || outside_cond,condition_curr,
    //         verified_new,verified);
    //     *verified = verified_new;
    //     let control = self.condition_stack.last_mut().unwrap();
    //     *control = condition_curr || outside_cond;
    // }
    // fn break_end_back(&mut self) {
    //     self.set_fndef(true);
    //     let control = self.condition_stack.last().unwrap();
    //     debug_assert!(control==&false,"under break, the condition and break-bool-flag must be false");
    // }
    // fn repeate_back(&mut self) {
    //     let Some(CorreE::Whc(Whileflow::While(offset))) = self.last() else {
    //         unreachable!("grammer error or jit error");
    //     };
    // }
}
// fn fill_jit_predicate(correspond:&mut CorrespondVec, frame:&mut Frame, symbols:&SymbolMap) {
//     if correspond.2.is_none() {
//         // no action for get if statement result
//         return ;
//     } 
//     assert!(correspond.is_running());

//     // if statement will consume the last value from frame data
//     // if no data in frame, panic
//     let last_value = frame.data.pop().unwrap();
//     let last_value = value_of(symbols, &last_value);
//     let Et::I32(last_value) = last_value else {
//         panic!("should not be running here");
//     };
//     let last_value = last_value != 0;
//     correspond.todo_fill(last_value);
// }

impl CondStack {
    const fn new()->CondStack {
        CondStack {
            cond_stack: Vec::new(),
        }
    }
    fn push(&mut self, flowbool:FlowBool) {
        self.cond_stack.push(flowbool);
    }
    fn pop(&mut self) {
        self.cond_stack.pop();
    }
    fn update_while(&mut self,state:WhileState) {
        let FlowBool::While(while_state,..) = self.cond_stack.last_mut().unwrap() else {
            unimplemented!("the state must be while state");
        };
        *while_state = state;
    }
    fn update_if(&mut self,state:IfState) {
        let FlowBool::If(if_state,..) = self.cond_stack.last_mut().unwrap() else {
            unimplemented!("the state must be if state");
        };
        *if_state = state;
    }
    fn last(&self)->Option<&FlowBool> {
        self.cond_stack.last()
    }
    fn last_mut(&mut self)->Option<&mut FlowBool> {
        self.cond_stack.last_mut()
    }
    fn is_empty(&self)->bool {
        self.cond_stack.is_empty()
    }
}
fn push_frame(frame_stack: &mut FrameVec)->&mut Frame {
    println!("(\n(----------> begin a new frame\n(");
    frame_stack.push(Frame::new());
    frame_stack.last_mut().unwrap()
}
fn pop_frame(frame_stack: &mut FrameVec)->Option<Frame> {
    println!(")\n)<---------- end a frame\n)");
    frame_stack.pop()
}

type FnCodeMap = BTreeMap<String,Fndef>;

/// Many design schemes tried:
/// 1 (corre,Flag(defcode,jitcode) // so much changes
/// 2 enum Code {Defcode(CorreE),Jitcode(CorreE)} // so much changes
/// 3 enum Lit{Litteral,Litteraling,None}, e|Litteral|e|e|Litteral|e|e|Litteraling(2)|, insert Flag; None indicating is the top is Lit
/// 4 def a Count in parse Exp, ++ --
/// 5 def a Stack in Parse Exp
/// 6 def a stack in Correspond(Vec<corre>,Vec(counter))
/// 7 def a count in Correspond(Vec, counter) // this is the final design tick tick tick 100%
/// 8 def a count in Correspond(Vec, bool-stack) // use one indicator for each layer, drop of the counter which let the progream be more complex 
/// the two states are mutually exclusive
// #[derive(Debug)]
// enum Verify {
//     Count(u32),
//     Pred(bool),
// }

/// condition put in AST structure, strictly saying, we should not
/// if we get the condition from the pop function, during the press, there
/// will be some data push into stack, happen in else point. There is no other
/// good method to skip it, the get will go a long way, so we need get the cond immediately! so embeded in CorreStrut
/// we use the back channel to update it, after the action procedure
/// this is the needed of the interpreted language
type FndefStack = usize;//Vec<(bool,bool)>;
struct CondBool(bool);
struct BreakBool(bool);
impl std::ops::Deref for CondBool {
    type Target = bool;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl std::ops::DerefMut for CondBool {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}
// struct BreakInfo {
//     is_break: bool,
//     break_size: usize,
// }
// type CondStack = Vec<FlowBool>;
#[derive(Debug)]
struct CondStack {
    cond_stack: Vec<FlowBool>,
    // break_info: BreakInfo,
    // is_break: bool,
    // break_size: usize,
}
#[derive(Debug)]
struct CorrespondVec {
    corre_stack: Vec<CorreE>,
    fndef_stack: FndefStack,
    exp_start: bool,
    // offset_stack: Vec<usize>,
    // condition_stack: Condition,
    // relocate_offset: Option<usize>,
}

struct Context {
    frame_stack: FrameVec,
    cond_stack: CondStack,
    symbols: SymbolMap,
    correspond: CorrespondVec,
    fn_codes: FnCodeMap,
}


