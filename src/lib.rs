
use std::collections::BTreeMap;


#[test]
pub fn test() {

    // let s = "1万3百20";
    // let s = "-5 * ( ( -3 + 6 ) )";
    // let s = r"
    // 64
    // 10913
    // 290
    // 176
    // 946
    // 2333
    // sum
    // ";
    let s = "31 cnt& cnt";
    let ss = s.to_string().as_str();
    // let s = "fn f x y = x+y";

    // let s = "sum 2 3 4";
    let s = s.chars().collect::<Box<[char]>>();
    let s = s.as_ref();
    // println!("====== {s:?}");
    // let a = &s[3];
    // let vv = parse_number(s);
    // let Some(vv) = parse_symbol(s) else {return};
    // let vv = parse_fn(s);

    let vv = parse(s);
    println!("==={vv:?}");
}

fn parse(src:&[char])->Option<Et> {
    let mut context = Context {
        frame_stack: Vec::<Frame>::new(),
        symbols: BTreeMap::new(),
    };
    context.frame_stack.push(Frame::new());

    let vv = parse_exp(&mut context, src);
    vv
}

fn parse_exp(context: &mut Context, src: &[char])->Option<Et> {
    let frame_stack = &mut context.frame_stack;

    if src.is_empty() {
        return None;
    }
    let mut src = src;

    println!("src: {src:?}");
    
    let rr = loop {
        let mut frame = frame_stack.last_mut().unwrap();
        let frame_empty = frame.data.is_empty() && frame.opi.is_empty();

        let Some((ut, src_rest)) = unit_next(src,frame_empty) else {
            // error
            return None;
        };
        // src = src_rest;

        let r = match ut {
            Ut::Ni(et) => {
                println!("++++>data: {:?} {:?}",et, src_rest);
                src = src_rest;
                push_data(Data::Val(et), &mut frame.data);
                None
            }

            Ut::Op(e,kind) => {
                if  frame.opi.last().is_none() ||
                    frame.opi.last().unwrap().0.prinum < e.prinum
                {
                    println!("++++>action: {:?} {:?}",e.name, src_rest);
                    src = src_rest;
                    push_action((e.clone(),kind), &mut frame.opi);
                    // 左目运算符，只和左边有关系，必须要执行
                    // 这个和有误返回值没有关系啦，统一了，;也统一了
                    if let DataWhere::Left(_) = e.data_where {
                        Some(e.prinum)
                    } else {
                        None
                    }
                } else {
                    Some(e.prinum)
                }
            }


            Ut::Pr(Pri::LBracket) => {
                src = src_rest;
                println!("====> {:?}",src);
                let frame_empty: Frame = Frame::new();
                frame_stack.push(frame_empty);
                frame = frame_stack.last_mut().unwrap();
                None
            }
            Ut::Pr(Pri::RBracket) => {
                src = src_rest;
                println!("=====> ****** {src:?}");
                Some(PriNum::Zero)
            }

            Ut::Sy(sym) => {
                src = src_rest;
                println!("++++> SYM {} {:?}", sym, src_rest);
                push_data(Data::Sym(sym), &mut frame.data);
                None
            }

            // Ut::Assign => {
            //     src = &src[1..];
            //     let frame_empty: Frame = Frame::new();
            //     frame_stack.push(frame_empty);
            //     frame = frame_stack.last_mut().unwrap();
            //     None
            // }

            Ut::End => {
                println!("==========> END {src:?}");
                Some(PriNum::Zero)
            }
        };

        if let Some(prinum) = r {
            try_pop_exp_util(&mut context.symbols,frame, prinum.clone());
            if prinum == PriNum::Zero && frame.opi.is_empty() {
                // assert_eq!(frame.data.len(),1);
                let vv = frame.data.last().cloned();
                frame_stack.pop();
                if let Some(last_frame) = frame_stack.last_mut() {
                    if let Some(vv) = vv {
                        last_frame.data.push(vv);
                    } else {
                        println!("***** nothing result with this frame");
                    }
                } else {
                    break vv;
                }
            }
        }
    };

    println!("return value = {rr:?}");
    let Some(Data::Val(rr)) = rr else {
        return None;
    };
    Some(rr)
}



type We = (char,i32);
const W : [We;3] = [('万',10000),('千',1000),('百',100)];
fn get_w(c:char, w:&[We])->Option<We> {
    let r = w.iter().find(|e|e.0==c);
    let r = r.map(|e|*e);
    r
}
#[derive(PartialEq,Debug,Clone, Copy)]
enum CT { Digit, Weight, }
fn ct(c:char)->Option<(CT,i32,i32)> {
    if c.is_ascii_digit() {
        Some((CT::Digit, 10, c as i32 - '0' as i32))
    } else if let Some(w) = get_w(c,&W) {
        Some((CT::Weight, w.1, 0))
    } else {
        None
    }
}
fn ct_digit(c:char)->Option<(CT,i32,i32)> {
    if c.is_ascii_digit() {
        Some((CT::Digit, 10, c as i32 - '0' as i32))
    } else {
        None
    }
}

type Wt = i32;
fn parse_number(chars:&[char])->Option<(i32,i32,Wt,&[char])> {
    let mut v = 0i32;
    let mut vv = v;
    let mut last_ct = CT::Digit;
    let mut index_next = 0;

    for c in chars {
        if SKIP_CHARS.contains(c) {
            index_next += 1;
            continue;
        } else {
            break;
        }
    }

    let chars = &chars[index_next..];
    index_next = 0;
    let mut sign = 1;
    let Some(c) = chars.first() else {
        return None;
    };
    const SIGN_FLAG: [(char, i32); 2] = [('+',1),('-',-1)];
    if let Some((_,sg)) = SIGN_FLAG.iter().find(|e|e.0 == *c) {
        index_next += 1;
        sign = *sg;
    }

    let chars = &chars[index_next..];
    index_next = 0;

    for c in chars {
        // println!("{c}");
        let Some((ct,w, c)) = ct(*c) else {
            break;
        };
        index_next += 1;
        if ct == CT::Digit && last_ct == CT::Weight {
            // println!("===>");
            vv += v;
            v = 0;
        }
        last_ct = ct;
        v = v*w + c;
        // println!("ct={ct:?} w={w} c={c} v={v} vv={vv}");
    }
    vv += v;

    let intergal_part = vv*sign;
    let chars = &chars[index_next..];
    if let Some('.') = chars.first() { } else {
        let r = Some((intergal_part,0,1,chars));
        return r;
    }

    let chars = &chars[1..];
    // 小数
    let mut v = 0;
    let mut vv = v;
    let mut ww = 1;
    // let mut last_ct = CT::Digit;
    let mut index_next = 0;
    for c in chars {
        // println!("{c}");
        let Some((_ct,w, c)) = ct_digit(*c) else {
            break;
        };
        ww *= w;
        index_next += 1;
        v = v*w + c;
        // println!("ct={ct:?} w={w} c={c} v={v} vv={vv}");
    }
    vv += v;

    let decimal_part = vv*sign;
    let decimal_weight = ww;
    let r = Some((intergal_part,decimal_part,decimal_weight,&chars[index_next..]));
    return r;
}

fn parse_symbol(src:&[char])->Option<(&[char],&[char])> {
    let mut index_next = 0;

    for c in src {
        if SKIP_CHARS.contains(c) {
            index_next += 1;
            continue;
        } else {
            break;
        }
    }

    let chars = &src[index_next..];
    index_next = 0;
    let Some(c) = chars.first() else {
        return None;
    };
    if !is_char(*c) {
        return None;
    }
    index_next += 1;

    // let chars = &chars[index_next..];
    // index_next = 0;

    for c in &chars[index_next..] {
        if !is_char_or_digit(*c) {
            break;
        }
        index_next += 1;
    }

    Some((&chars[..index_next],&chars[index_next..]))
}

fn skip_blank(src:&[char])->(&[char],Option<char>) {
    let mut index_next = 0;
    let mut char_next = None;

    for c in src {
        if SKIP_CHARS.contains(c) {
            index_next += 1;
            continue;
        } else {
            char_next = Some(*c);
            break;
        }
    }
    let src = &src[index_next..];
    
    assert!(!(char_next.is_none() ^ src.is_empty()));
    (src, char_next)
}

fn parse_fn(src:&[char])->Option<(&[char],Vec<&[char]>,&[char])> {

    let (src,_char_next) = skip_blank(src);

    // 如果不是fn 返回出错
    if !src.starts_with(&['f','n']) {
        return None;
    }
    let src = &src[2..];


    let Some((name,rest)) = parse_symbol(src) else {
        return None;
    };
    let mut src = rest;

    let mut ps = vec![];
    while let Some((p,rest)) = parse_symbol(src) {
        // let sym = sym.iter().collect::<String>();
        ps.push(p);
        src = rest;
    }

    let (src, Some('=')) = skip_blank(src) else {
        return None;
    };

    let body = &src[1..];
    let (body,_char) = skip_blank(body);

    Some((name, ps, body))
}

#[derive(Clone, Copy,Debug)]
enum Et {
    I32(i32),
    Real(f32)
}
type SymbolMap = BTreeMap<String,Et>;

#[derive(Clone)]
enum Act {
    Add(fn(&SymbolMap,&[Data])->Et),
    Sub(fn(&SymbolMap,&[Data])->Et),
    Mul(fn(&SymbolMap,&[Data])->Et),
    Div(fn(&SymbolMap,&[Data])->Et),
    Ass(fn(&mut SymbolMap,&[Data])->Et),
    NoRet(fn(&[Data])),
    Fn(fn(&mut SymbolMap,&[Data])->Et), // 自定义函数
}
impl Act {
    fn cal2(&self,symbol:&SymbolMap,d:&[Data]) -> Et {
        match self {
            Act::Add(f)
            |Act::Sub(f)
            |Act::Mul(f)
            |Act::Div(f) => f(symbol,d),
            _ => panic!(""),
        }
    }
    fn call2_mut(&self,symbol:&mut SymbolMap,d:&[Data]) -> Et {
        match self {
            Act::Add(f)
            |Act::Sub(f)
            |Act::Mul(f)
            |Act::Div(f) => f(symbol,d),
            Act::Ass(f) => f(symbol,d),
            _ => panic!(),
        }
    }
    fn call_noret(&self,d:&[Data]) {
        match self {
            Act::NoRet(f) => f(d),
            _ => panic!(),
        }
    }
    fn call_slice(&self,symbol:&mut SymbolMap,d:&[Data])->Et {
        match self {
            Act::Fn(f) => f(symbol,d),
            _ => unreachable!(),
        }
    }
}
#[derive(Clone)]
enum Pri {
    LBracket,
    RBracket,
}
const PRI_UT: [(char, Ut); 2] = [
    ('(', Ut::Pr(Pri::LBracket)),
    (')', Ut::Pr(Pri::RBracket))
];

#[derive(Clone, Copy)]
enum Para {
    Consumed,
    Ref,
}

#[derive(Clone)]
enum Ut {
    Ni(Et),
    Op(Opi,Para),
    Pr(Pri),
    Sy(String),
    End
}

#[derive(Clone,PartialEq)]
enum DataWhere {
    Zero,
    Any(i32),
    Left(i32),
    Right(i32),
    Both(i32,i32),
    Mid(i32),
}

#[derive(Clone,PartialEq, PartialOrd)]
enum PriNum {
    Zero, // )
    One, // = ;
    Two, // + -
    Three, // * /
    Four, // (
}

#[derive(Clone, Copy)]
enum Ret {
    Value,
    None,
}

#[derive(Clone)]
struct Opi {
    name: &'static[char],
    act: Act,
    prinum: PriNum,
    data_where: DataWhere,
    ret: Ret,
    pred: char, // data
}
impl Opi {
    const fn new(name:&'static[char], act:Act, prinum: PriNum, data_where:DataWhere, ret:Ret)->Self {
        Self {name, act, prinum,data_where, ret, pred:' '}
    }
}

fn value_of(symbol:&BTreeMap<String,Et>,d:&Data)->Et {
    let value = match d {
        Data::Val(e) => e,
        Data::Sym(e) => &symbol[e],
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
            Et::Real(_) => todo!(),
        };
        let e2 = match rhs {
            Et::I32(e) => e,
            Et::Real(_) => todo!(),
        };
        Self::I32(e1+e2)
    }
}
impl std::ops::Sub for Et {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        let e1 = match self {
            Et::I32(e) => e,
            Et::Real(_) => todo!(),
        };
        let e2 = match rhs {
            Et::I32(e) => e,
            Et::Real(_) => todo!(),
        };
        Self::I32(e1-e2)
    }
}
impl std::ops::Mul for Et {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        let e1 = match self {
            Et::I32(e) => e,
            Et::Real(_) => todo!(),
        };
        let e2 = match rhs {
            Et::I32(e) => e,
            Et::Real(_) => todo!(),
        };
        Self::I32(e1*e2)
    }
}
impl std::ops::Div for Et {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        let e1 = match self {
            Et::I32(e) => e,
            Et::Real(_) => todo!(),
        };
        let e2 = match rhs {
            Et::I32(e) => e,
            Et::Real(_) => todo!(),
        };
        Self::I32(e1/e2)
    }
}

fn add (symbol:&BTreeMap<String,Et>,d:&[Data])->Et {
    let v1 = value_of(symbol, &d[1]);
    let v2 = value_of(symbol, &d[0]);
    v1+v2
}
fn sub (symbol:&BTreeMap<String,Et>,d:&[Data])->Et {
    let v1 = value_of(symbol, &d[1]);
    let v2 = value_of(symbol, &d[0]);
    v1-v2
}
fn mul (symbol:&BTreeMap<String,Et>,d:&[Data])->Et {
    let v1 = value_of(symbol, &d[1]);
    let v2 = value_of(symbol, &d[0]);
    v1*v2
}
fn div (symbol:&BTreeMap<String,Et>,d:&[Data])->Et {
    let v1 = value_of(symbol, &d[1]);
    let v2 = value_of(symbol, &d[0]);
    v1/v2
}
fn assign (symbol:&mut BTreeMap<String,Et>,d:&[Data])->Et {
    let v2 = *d[1].as_et();
    let _old = match &d[0] {
        Data::Sym(e) => symbol.insert(e.clone(), v2),
        _ => panic!(""),
    };
    v2
}
fn no_return(_:&[Data]) {
    // let ss = "".parse();
    // let ss = ss.ok();
}

fn sum (symbol:&mut BTreeMap<String,Et>,data:&[Data])->Et {
    let r = data.iter().map(
        |e|
        match e {
            Data::Sym(e) =>
                if let Et::I32(e) = symbol[e] {e} else {panic!()},
            Data::Val(e) =>
                if let Et::I32(e) = e {*e} else {panic!()},
        } 
    ).sum::<i32>();
    Et::I32(r)
}

fn cnt (_symbol:&mut BTreeMap<String,Et>,data:&[Data])->Et {
    Et::I32(data.len() as i32)
}


const OPS:[Opi;8] = [
    Opi::new(&['+'],Act::Add(add),PriNum::Two,DataWhere::Any(2),Ret::Value),
    Opi::new(&['-'],Act::Sub(sub),PriNum::Two,DataWhere::Any(2),Ret::Value),
    Opi::new(&['*'],Act::Mul(mul),PriNum::Three,DataWhere::Any(2),Ret::Value),
    Opi::new(&['/'],Act::Div(div),PriNum::Three,DataWhere::Any(2),Ret::Value),
    Opi::new(&['='],Act::Ass(assign),PriNum::One,DataWhere::Any(2),Ret::Value),
    Opi::new(&[';'],Act::NoRet(no_return),PriNum::One,DataWhere::Left(1),Ret::None),
    Opi::new(&['s','u','m'],Act::Fn(sum),PriNum::Four,DataWhere::Any(-1),Ret::Value),
    Opi::new(&['c','n','t'],Act::Fn(cnt),PriNum::Four,DataWhere::Any(-1),Ret::Value),
    ];

#[derive(Clone,Debug)]
enum Data {
    Val(Et),
    Sym(String)
}
struct Frame {
    data: Vec<Data>,
    opi: Vec<(Opi,Para)>
}

impl Frame {
    fn new() -> Self {
        Self {data:Vec::new(),opi:Vec::new()}
    }
}

macro_rules! DIGITS { () => {'0'..='9'}; }
macro_rules! LOWER_CHARS { () => {'a'..='z'}; }
macro_rules! UPPER_CHARS { () => {'A'..='Z'}; }

const DIGITS: std::ops::RangeInclusive<char> = DIGITS!();
const LOWER_CHARS: std::ops::RangeInclusive<char> = LOWER_CHARS!();
const UPPER_CHARS: std::ops::RangeInclusive<char> = UPPER_CHARS!();
fn is_char(c:char)-> bool {
    match c {
        LOWER_CHARS!() | UPPER_CHARS!() => true,
        _ => false,
    }
}
fn is_char_or_digit(c:char)->bool {
    match c {
        LOWER_CHARS!() | UPPER_CHARS!() | DIGITS!() => true,
        _ => false,
    }
}

#[cfg(never)]
fn which(c:char)->Option<Ut> {
    fn opof(c:char)->Option<Opi> {
        let r = OPS.iter().find(|e|e.name[0] == c);
        let r = r.cloned();
        r
    }

    if DIGITS.contains(&c) {
        Some(Ut::Ni)
    } else if let Some(opi) = opof(c) {
        Some(Ut::Op(opi))
    } else if c == '(' {
        Some(Ut::Pr(Pri::LBracket))
    } else if c == ')' {
        Some(Ut::Pr(Pri::RBracket))
    } else if is_char(c) {
        Some(Ut::Sy)
    } else {
        None
    }
}
const SKIP_CHARS:[char;3] = [' ','\r','\n'];

struct Unit<'a> {
    ut: Ut,
    src_next: &'a[char],
    
}

fn unit_next(src:&[char], frame_empty:bool)->Option<(Ut,&[char])> {
    // let mut src = src;

    // // skip ignored char
    // let c = loop {
    //     let Some(c) = src.first() else {
    //         // <5> END
    //         return Some((Ut::End,&src[0..0]));
    //     };
    //     if SKIP_CHARS.contains(c) {
    //         src = &src[1..];
    //     } else {
    //         break c;
    //     }
    // };

    // skip ignored char
    let (src,Some(ref c)) = skip_blank(src) else {
        return Some((Ut::End,src));
    };

    // 处理 开始的正负号，先不以单目运算符进行解析
    // the first + - maybe is number if next char is in 0-9
    if frame_empty {
        if let '+'|'-' = c {
            if let Some(DIGITS!()) = src.get(1) {
                if let Some((ni,_deci,_w,src_rest)) = parse_number(src) {
                    return Some((Ut::Ni(Et::I32(ni)),src_rest));
    }   }   }   }

    // <1> 12345.0123
    if DIGITS.contains(c) {
        if let Some((ni,_deci,_w,src_rest)) = parse_number(src) {
            println!("number parsed is {ni}+{} = {_deci}/{_w}", _deci as f32/_w as f32);
            return Some((Ut::Ni(Et::I32(ni)),src_rest));
        }
    // <2> +-*/=;sum cnt
    } if let Some(op) = OPS.iter().find(|e|src.starts_with(e.name)) {
        assert!(src.len()>=op.name.len());
        let name_len = op.name.len();
        let kind = if let Some('&') = src.get(name_len) {
            (Para::Ref,name_len+1)
        } else {
            (Para::Consumed,name_len)
        };
        return Some((Ut::Op(op.clone(),kind.0),&src[kind.1..]));
    // <3> ( )
    } else if let Some((_,ut)) = PRI_UT.iter().find(|e|e.0==*c) {
        assert!(src.len()>=1);
        return Some((ut.clone(),&src[1..]))
    // <4> symbol
    } else if UPPER_CHARS.contains(c) || LOWER_CHARS.contains(c) {
        if let Some((sym,src_rest)) = parse_symbol(src) {
            let sym = sym.iter().collect::<String>();
            return Some((Ut::Sy(sym),src_rest));
        }
    }
    // Error, we canot diagonise
    None
}

fn push_data(v:Data, stack: &mut Vec<Data>) {
    stack.push(v);
}
fn push_action(opi:(Opi,Para), stack: &mut Vec<(Opi,Para)>) {
    stack.push(opi);
}

fn try_pop_exp_util(symbol:&mut SymbolMap,frame: &mut Frame, prinum:PriNum) {
    while let Some(last_op) = frame.opi.last() {
        if last_op.0.prinum >= prinum {
            pop_exp(symbol,frame);
        } else {
            break;
        }
    }
}
fn pop_exp(symbol:&mut SymbolMap,frame: &mut Frame) {
    let Some(opi) = frame.opi.pop() else {
        return;
    };
    match opi.0.ret {
        Ret::Value => {
            match opi.0.data_where {
                DataWhere::Any(2) => {
                    let len = frame.data.len();
                    let d = frame.data.get(len-2..len).unwrap();
                    // let d2 = frame.data.pop().unwrap();
                    // let d1 = frame.data.pop().unwrap();
                    println!("      {:?}({d:?})",opi.0.name);
                    let d3 = opi.0.act.call2_mut(symbol, d);
                    if let Para::Consumed = opi.1 {
                        frame.data.pop().unwrap();
                        frame.data.pop().unwrap();
                    }
                    if let Ret::Value = opi.0.ret {
                        frame.data.push(Data::Val(d3));
                    }
                }
                DataWhere::Any(-1) => {
                    let d = frame.data.as_slice();
                    let d3 = opi.0.act.call_slice(symbol, d);
                    println!("      {:?}({d:?})",opi.0.name);
                    if let Para::Consumed = opi.1 {
                        frame.data.clear();
                    }
                    if let Ret::Value = opi.0.ret {
                        frame.data.push(Data::Val(d3));
                    }
                }
                _ => {}
            }
        }
        Ret::None => {
            match opi.0.data_where {
                DataWhere::Left(1) => {
                    let len = frame.data.len();
                    let d = frame.data.get(len-1..len).unwrap();
                    println!("      {:?}({d:?})",opi.0.name);
                    let _d = opi.0.act.call_noret(d);
                    if let Para::Consumed = opi.1 {
                        frame.data.pop().unwrap();
                    }
                }
                _ => {}
            }
        }
    }
}


struct Context {
    frame_stack: Vec<Frame>,
    symbols: SymbolMap
}


