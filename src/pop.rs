use std::collections::BTreeMap;

use crate::{
    parse_fn_exp,
    FnCodeMap, Frame, SymbolMap,
};
use crate::token::ToChars; 
use crate::ast::Sym;
use crate::push::{FlowBool, IfState, WhileState};
use crate::types::{Data, Et, PriNum, RetRule};




pub(crate) fn decide_todo(subject_matter:PopSubjectMatter,codes:&FnCodeMap,symbols:&mut SymbolMap, frame: &mut Frame)->Option<()> {
    // the two functions just use in this function
    fn pop_last_and_clear(stack: &mut Vec<Data>, symbols:&SymbolMap)->Et {
        let data = stack.pop().unwrap();
        stack.clear();
        value_of(symbols, &data)
    }
    fn clear_data(frame:&mut Frame) {
        debug_assert!(frame.opi.is_empty());
        frame.data.clear();
    }

    match subject_matter {
        PopSubjectMatter::Op(op, param) => {
            let cause = (op.prinum,RetRule::Ignore);
            try_pop_exp_util(codes,symbols,frame,cause);
            frame.opi.push((op,param));
            None
        },
        PopSubjectMatter::Pr(prinum,retrule) =>{
            let cause = (prinum,retrule);
            try_pop_exp_util(codes,symbols,frame,cause);
            // P0 means the end of the program
            if let PriNum::P0|PriNum::P1 = prinum {Some(())} else {None}
        }
        PopSubjectMatter::PrCond(prinum, retrule, act,flowbool) => {
            debug_assert_eq!(prinum,PriNum::P2);
            let cause = (prinum,retrule);
            try_pop_exp_util(codes,symbols,frame,cause);
            let data_bool = pop_last_and_clear(&mut frame.data, symbols).as_bool();
            act(data_bool,flowbool);
            None
        }
        PopSubjectMatter::PrAgain(prinum,_retrule,..) => {
            debug_assert_eq!(prinum,PriNum::P2);
            let cause = (prinum,RetRule::Ignore);
            try_pop_exp_util(codes,symbols,frame,cause);
            clear_data(frame);
            None
        }
        PopSubjectMatter::Donot => None, // do nothing
    }
}


fn try_pop_exp_util(codes:&FnCodeMap,symbol:&mut SymbolMap,frame: &mut Frame, cause:(PriNum,RetRule)) {
    let (prinum,lastret) = cause;
    while let Some((last_op,_last_para)) = frame.opi.last() {
        if last_op.prinum >= prinum {
            let is_op_last = frame.opi.len()==1;
            let retrule = if let (RetRule::None,true) = (&lastret,is_op_last)
                {RetRule::None} else {RetRule::Ignore}; 
            pop_exp(codes,symbol,frame,retrule);
        } else {
            break;
        }
    }
}

fn pop_exp(codes:&FnCodeMap,symbol:&mut SymbolMap,frame: &mut Frame, retrule:RetRule)->Option<()> {
    let Some(opi) = frame.opi.pop() else {
        return None;
    };
    println!("\t----> acton:{:?}{:?}->{:?} ({:?})", opi.0.name,opi.1,retrule,frame.data);
    let d;
    match opi.0.data_where {
        DataWhere::Zero => d = [].as_slice(),
        DataWhere::Any(-1) => {
            d = frame.data.as_slice();
            // println!("\t1:param cnt: {0}/{0}",d.len());
        }
        DataWhere::Any(n) | DataWhere::Left(n)=> {
            let n = n as usize;
            let len = frame.data.len();
            // println!("\t2:param cnt: {n}/{}",len);
            d = frame.data.get(len-n..len).unwrap();
        }
        DataWhere::Right(_) => todo!(),
        DataWhere::Both(_, _) => todo!(),
        DataWhere::Mid(_) => todo!(),
    }

    let d3; // return value
    match opi.0.act {
        Act::Add(_)|Act::Sub(_)|Act::Mul(_)|Act::Div(_)|Act::Ass(_)|
        Act::Ge(_)|Act::Gt(_)|Act::Le(_)|Act::Lt(_)|Act::Eq(_)|Act::Ne(_)|Act::Cmp(_)|
        Act::And(_)|Act::Or(_)|Act::Not(_)
            => d3 = Some(opi.0.act.call(symbol, d)),
        Act::Opfn(_)
            => d3 = Some(opi.0.act.call_opfn(symbol, d)),
        Act::Fn(_) => {
            // HERE, happens cracked, when we call name.str
            // let Sym::String(ref name) = opi.0.name else {
            //     panic!("the name is not String");
            // };
            let Sym::String(name) = opi.0.name else {
                panic!("the name is not String");
            };
            let name = name.as_str();
            d3 = Some(opi.0.act.call_fn(name, codes, symbol, d));
        }
        // Act::Aux(_) => {
        //     d3 = None;
        //     println!("      {:?}({d:?})",opi.0.name);
        //     unreachable!("the code would not be runned here");
        // }
    }

    // println!("\t4:{:?} pop {}",opi.1,d.len());
    // pop param if necessary
    if let Para::Consumed = opi.1 {
        for _ in 0..d.len() {
            frame.data.pop().unwrap();
        }
    }

    // return value
    // println!("\t5:={:?} {:?}",d3,opi.0.ret);
    if let (Ret::Value,RetRule::Ignore) = (opi.0.ret,retrule) {
        if let Some(d3) = d3 {
            frame.data.push(Data::Val(d3));
        }
    }

    println!("\t\t=> {:?}  ... left {:?}",d3,frame.data);
    Some(())
}




// enum AndTodoNext {
//     TrueDo, FalseDo,
// }
#[derive(Debug)]
pub(crate) enum PopSubjectMatter<'a> {
    Op(Opi,Para),
    Pr(PriNum,RetRule),
    PrCond(PriNum,RetRule,fn(bool,&mut FlowBool),&'a mut FlowBool),
    PrAgain(PriNum,RetRule,usize,usize), // offset
    // ConditionCalc(PriNum),
    // BreakCalc(PriNum),
    Donot,
}
pub(crate) fn do_if_then(cond:bool, flowbool:& mut FlowBool) {
    let FlowBool::If(ifstate@IfState::If0,..) = flowbool else {
        panic!("the grammmer error");
    };
    if cond {
        *ifstate = IfState::ThenDo;
    } else {
        *ifstate = IfState::ThenDonot;
    }
}
pub(crate) fn do_if_else(cond:bool, flowbool:& mut FlowBool) {
    let FlowBool::If(ifstate@IfState::If0,..) = flowbool else {
        panic!("the grammmer error");
    };
    if !cond {
        *ifstate = IfState::ElseDo;
    } else {
        *ifstate = IfState::ElseDonot;
    }
}

fn do_if_ast_null(_cond:bool, _flowbool:& mut FlowBool) {
}

pub(crate) fn do_while_body<'a>(cond:bool, flowbool:&'a mut FlowBool) {
    let FlowBool::While(whilestate@WhileState::While1,..) = flowbool else {
        panic!("the grammmer error");
    };
    if cond {
        *whilestate = WhileState::BodyDo;
    } else {
        *whilestate = WhileState::BodyDonot;
    }
}

enum AndTodo {
    Try,
    None,
    ConditionBack(bool),
    BreakBack, // donot need the break value, just store in the frame, get the value at the while-end
}


#[derive(Debug,Clone,PartialEq)]
pub(crate) enum DataWhere {
    Zero,
    Any(i32),
    Left(i32),
    Right(i32),
    Both(i32,i32),
    Mid(i32),
}


#[derive(Clone, Copy,Debug)]
pub(crate) enum Para {
    Consumed,
    Ref,
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum Ret {
    Value,
    None,
}

#[derive(Debug,Clone)]
pub(crate) struct Opi {
    pub(crate) name: Sym,//&'static[char],
    pub(crate) act: Act,
    pub(crate) prinum: PriNum,
    data_where: DataWhere,
    ret: Ret,
    pred: char, // data
}
impl Opi {
    pub(crate) const fn new(name:Sym, act:Act, prinum: PriNum, data_where:DataWhere, ret:Ret)->Self {
        Self {name, act, prinum,data_where, ret, pred:' '}
    }
    pub(crate) const fn from_fn(sym:String,ps_cnt:usize)-> Self {
        let fn_name = Sym::String(sym);
        let fn_dw = DataWhere::Any(ps_cnt as i32);
        const FN_PRINUM: PriNum = PriNum::P10;
        const FN_DO: Act = Act::Fn(op_fn_do);
        const FN_RET: Ret = Ret::Value;
        Self::new(fn_name, FN_DO, FN_PRINUM, fn_dw, FN_RET)
    }
}
impl ToChars for Opi {
    fn to_chars(&self)->&[char] {
        let Sym::Str(name) = self.name else {
            unreachable!("");
        };
        name
    }
}

fn value_of(symbols:&BTreeMap<String,Et>,d:&Data)->Et {
    let value = match d {
        Data::Val(e) => e,
        Data::Sym(e) => &symbols[e],
    };
    *value
}
impl Data {
    fn as_et(&self)->&Et {
        let Data::Val(e) = self else {
            panic!("");
        };
        e
    }
}

impl std::ops::Add for Et {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        let e1 = match self {
            Et::I32(e) => e,
            _ => todo!(),
        };
        let e2 = match rhs {
            Et::I32(e) => e,
            _ => todo!(),
        };
        Self::I32(e1+e2)
    }
}
impl std::ops::Sub for Et {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        let e1 = match self {
            Et::I32(e) => e,
            _ => todo!(),
        };
        let e2 = match rhs {
            Et::I32(e) => e,
            _ => todo!(),
        };
        Self::I32(e1-e2)
    }
}
impl std::ops::Mul for Et {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        let e1 = match self {
            Et::I32(e) => e,
            _ => todo!(),
        };
        let e2 = match rhs {
            Et::I32(e) => e,
            _ => todo!(),
        };
        Self::I32(e1*e2)
    }
}
impl std::ops::Div for Et {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        let e1 = match self {
            Et::I32(e) => e,
            _ => todo!(),
        };
        let e2 = match rhs {
            Et::I32(e) => e,
            _ => todo!(),
        };
        Self::I32(e1/e2)
    }
}

impl Et {
    const fn as_bool(&self)->bool {
        let Et::I32(0) = self else {
            return true;
        };
        false
    }
}

fn op_add (symbol:&BTreeMap<String,Et>,d:&[Data])->Et {
    let v1 = value_of(symbol, &d[0]);
    let v2 = value_of(symbol, &d[1]);
    v1+v2
}
fn op_sub (symbol:&BTreeMap<String,Et>,d:&[Data])->Et {
    let v1 = value_of(symbol, &d[0]);
    let v2 = value_of(symbol, &d[1]);
    v1-v2
}
fn op_mul (symbol:&BTreeMap<String,Et>,d:&[Data])->Et {
    let v1 = value_of(symbol, &d[0]);
    let v2 = value_of(symbol, &d[1]);
    v1*v2
}
fn op_div (symbol:&BTreeMap<String,Et>,d:&[Data])->Et {
    let v1 = value_of(symbol, &d[0]);
    let v2 = value_of(symbol, &d[1]);
    v1/v2
}
fn op_assign (symbol:&mut BTreeMap<String,Et>,d:&[Data])->Et {
    let v2 = *d[1].as_et();
    let _old = match &d[0] {
        Data::Sym(e) => symbol.insert(e.clone(), v2),
        _ => panic!(""),
    };
    v2
}
// fn no_return(_:&[Data]) {
//     // let ss = "".parse();
//     // let ss = ss.ok();
// }

fn op_sum (symbol:&mut BTreeMap<String,Et>,data:&[Data])->Et {
    let r = data.iter().map(
        |d| *value_of(symbol, d).as_i32()
    ).sum::<i32>();
    Et::I32(r)
}

fn op_cnt (_symbol:&mut BTreeMap<String,Et>,data:&[Data])->Et {
    Et::I32(data.len() as i32)
}

fn op_avg (symbol:&mut BTreeMap<String,Et>,data:&[Data])->Et {
    let Et::I32(sum) = op_sum(symbol,data) else {
        panic!("not supports non i32");
    };
    let n = data.len() as i32;
    Et::I32(sum/n)
}

// fn op_fn_def(src:&[char])->Option<(&[char],&[char])> {
//     let Some((_name,ref _ps,body, rest)) = parse_fn_def(src) else {
//         return None;
//     };
//     Some((body, rest))
// }

pub(crate) fn op_fn_do(fn_name:&str,codes:&FnCodeMap,symbol:&BTreeMap<String,Et>,data:&[Data])->Et {
    let mut ps = Vec::new();
    for d in data {
        let v = value_of(symbol, d);
        ps.push(v);
    }
    let fn_def = codes[fn_name].clone();
    let ps = ps.as_slice();
    let Some(et) = parse_fn_exp(fn_def, ps) else {
        panic!("run cracked");
    };
    et
}
fn op_gt (symbol:&BTreeMap<String,Et>,d:&[Data])->Et {
    let v1 = value_of(symbol, &d[0]);
    let v2 = value_of(symbol, &d[1]);
    Et::I32((v1 > v2) as i32)
}
fn op_ge (symbol:&BTreeMap<String,Et>,d:&[Data])->Et {
    let v1 = value_of(symbol, &d[0]);
    let v2 = value_of(symbol, &d[1]);
    Et::I32((v1 >= v2) as i32)
}
fn op_lt (symbol:&BTreeMap<String,Et>,d:&[Data])->Et {
    let v1 = value_of(symbol, &d[0]);
    let v2 = value_of(symbol, &d[1]);
    Et::I32((v1 < v2) as i32)
}
fn op_le (symbol:&BTreeMap<String,Et>,d:&[Data])->Et {
    let v1 = value_of(symbol, &d[0]);
    let v2 = value_of(symbol, &d[1]);
    Et::I32((v1 <= v2) as i32)
}
fn op_eq (symbol:&BTreeMap<String,Et>,d:&[Data])->Et {
    let v1 = value_of(symbol, &d[0]);
    let v2 = value_of(symbol, &d[1]);
    Et::I32((v1 == v2) as i32)
}
fn op_ne (symbol:&BTreeMap<String,Et>,d:&[Data])->Et {
    let v1 = value_of(symbol, &d[0]);
    let v2 = value_of(symbol, &d[1]);
    Et::I32((v1 != v2) as i32)
}
fn op_cmp (symbol:&BTreeMap<String,Et>,d:&[Data])->Et {
    let v1 = value_of(symbol, &d[0]);
    let v2 = value_of(symbol, &d[1]);
    Et::I32((v1.partial_cmp(&v2).unwrap()) as i32)
}
fn op_and (symbol:&BTreeMap<String,Et>,d:&[Data])->Et {
    let v1 = value_of(symbol, &d[0]);
    let v2 = value_of(symbol, &d[1]);
    Et::I32((v1.as_bool() && v2.as_bool()) as i32)
}
fn op_or (symbol:&BTreeMap<String,Et>,d:&[Data])->Et {
    let v1 = value_of(symbol, &d[0]);
    let v2 = value_of(symbol, &d[1]);
    Et::I32((v1.as_bool() || v2.as_bool()) as i32)
}
fn op_not (symbol:&BTreeMap<String,Et>,d:&[Data])->Et {
    let v1 = value_of(symbol, &d[0]);
    Et::I32((!v1.as_bool()) as i32)
}

// fn start_with(str:&[char],sub:&[char],)->()
// 如何初始化这个，的确得想想，Lazystatic好呀，不用锁，最长匹配优先
pub(crate) const OPS:[Opi;18] = [
    // put here, for the longest match
    Opi::new(Sym::Str(&['=','=']),Act::Eq(op_eq),PriNum::P7,DataWhere::Any(2),Ret::Value),
    Opi::new(Sym::Str(&['=']),Act::Ass(op_assign),PriNum::P3,DataWhere::Any(2),Ret::Value),

    Opi::new(Sym::Str(&['o','r']),Act::Or(op_or),PriNum::P4,DataWhere::Any(2),Ret::Value),

    Opi::new(Sym::Str(&['a','n','d']),Act::And(op_and),PriNum::P5,DataWhere::Any(2),Ret::Value),

    Opi::new(Sym::Str(&['>','=']),Act::Ge(op_ge),PriNum::P6,DataWhere::Any(2),Ret::Value),
    Opi::new(Sym::Str(&['>']),Act::Gt(op_gt),PriNum::P6,DataWhere::Any(2),Ret::Value),
    // put here for the longest match
    Opi::new(Sym::Str(&['<','=']),Act::Le(op_le),PriNum::P6,DataWhere::Any(2),Ret::Value),
    Opi::new(Sym::Str(&['<']),Act::Lt(op_lt),PriNum::P6,DataWhere::Any(2),Ret::Value),

    Opi::new(Sym::Str(&['!','=']),Act::Ne(op_ne),PriNum::P7,DataWhere::Any(2),Ret::Value),
    // Opi::new(Sym::Str(&['=','=']),Act::Eq(eq),PriNum::P7,DataWhere::Any(2),Ret::Value),
    Opi::new(Sym::Str(&['c','m','p']),Act::Cmp(op_cmp),PriNum::P7,DataWhere::Any(2),Ret::Value),

    Opi::new(Sym::Str(&['s','u','m']),Act::Opfn(op_sum),PriNum::P8,DataWhere::Any(-1),Ret::Value),
    Opi::new(Sym::Str(&['a','v','g']),Act::Opfn(op_avg),PriNum::P8,DataWhere::Any(-1),Ret::Value),

    Opi::new(Sym::Str(&['+']),Act::Add(op_add),PriNum::P9,DataWhere::Any(2),Ret::Value),
    Opi::new(Sym::Str(&['-']),Act::Sub(op_sub),PriNum::P9,DataWhere::Any(2),Ret::Value),

    Opi::new(Sym::Str(&['*']),Act::Mul(op_mul),PriNum::P10,DataWhere::Any(2),Ret::Value),
    Opi::new(Sym::Str(&['/']),Act::Div(op_div),PriNum::P10,DataWhere::Any(2),Ret::Value),

    Opi::new(Sym::Str(&['n','o','t']),Act::Not(op_not),PriNum::P11,DataWhere::Any(1),Ret::Value),
    Opi::new(Sym::Str(&['c','n','t']),Act::Opfn(op_cnt),PriNum::P11,DataWhere::Any(-1),Ret::Value),
    //     Opi::new(Sym::Str(&['<','=']),Act::Le(le),PriNum::Three,DataWhere::Any(2),Ret::Value),
    ];
    // const OOO: [Opi;2] = ops();

// const ssss:[Opi;2] = [
//     Opi::new(Sym::Str(&['=']),Act::Mul(mul),PriNum::P9,DataWhere::Any(2),Ret::Value),
//     Opi::new(Sym::Str(&['=','=']),Act::Mul(mul),PriNum::P9,DataWhere::Any(2),Ret::Value)
//     ];
// const sssd:[Opi:2] = [
    
// ];
// static AA:std::cell::OnceCell<[&Opi;2]> =
// use std::sync::LazyLock;
// fn fff() {
// let  BBB = LazyLock::new(||ops(&ssss));
// }
// fn ops(sss:&[Opi;2])->[&Opi;2] {
//     let aa = sss.each_ref();
//     aa
//     // let bb = sss.as_ref();
//     // let cc = bb.
//     // bb
// }

#[derive(Clone,Debug)]
pub(crate) enum Act {
    Ass(fn(&mut SymbolMap,&[Data])->Et),

    Or(fn(&SymbolMap,&[Data])->Et),

    And(fn(&SymbolMap,&[Data])->Et),

    Gt(fn(&SymbolMap,&[Data])->Et),
    Ge(fn(&SymbolMap,&[Data])->Et),
    Lt(fn(&SymbolMap,&[Data])->Et),
    Le(fn(&SymbolMap,&[Data])->Et),

    Ne(fn(&SymbolMap,&[Data])->Et),
    Eq(fn(&SymbolMap,&[Data])->Et),

    Cmp(fn(&SymbolMap,&[Data])->Et),

    Add(fn(&SymbolMap,&[Data])->Et),
    Sub(fn(&SymbolMap,&[Data])->Et),

    Mul(fn(&SymbolMap,&[Data])->Et),
    Div(fn(&SymbolMap,&[Data])->Et),

    Not(fn(&SymbolMap,&[Data])->Et),

    Opfn(fn(&mut SymbolMap,&[Data])->Et), // 系统内定义函数
    Fn(fn(&str,&FnCodeMap,&SymbolMap,&[Data])->Et),
}
impl Act {
    fn call(&self,symbol:&mut SymbolMap,d:&[Data]) -> Et {
        match self {
            Act::Ass(f)
            => f(symbol,d),
            Act::Add(f)|
            Act::Sub(f)|
            Act::Mul(f)|
            Act::Div(f)|
            Act::Gt(f)|
            Act::Ge(f)|
            Act::Lt(f)|
            Act::Le(f)|
            Act::Eq(f)|
            Act::Ne(f)|
            Act::Cmp(f)|
            Act::And(f)|
            Act::Or(f)|
            Act::Not(f)
            => f(symbol,d),
            _ => panic!(),
        }
    }
    // fn call_aux(&self,_d:&[Data]) {
    // }
    fn call_opfn(&self,symbol:&mut SymbolMap,d:&[Data])->Et {
        match self {
            Act::Opfn(f) => f(symbol,d),
            _ => unreachable!(),
        }
    }
    fn call_fn(&self,name:&str,codes:&FnCodeMap,symbol:&BTreeMap<String,Et>,d:&[Data])->Et {
        match self {
            Act::Fn(f) => f(name,codes,symbol,d),
            _ => unreachable!(),
        }
    }
}


