use std::{cmp::Ordering, collections::BTreeMap};

#[test]
fn test_enun_next() {
    const fn next_pri(p:PriNum)->PriNum {
        match p {
            PriNum::P0 => PriNum::P1,
            PriNum::P1 => PriNum::P2,
            PriNum::P2 => PriNum::P3,
            PriNum::P3 => PriNum::P4,
            PriNum::P4 => PriNum::P5,
            PriNum::P5 => PriNum::P5,
            PriNum::P6 => PriNum::P7,
            PriNum::P7 => PriNum::P8,
            PriNum::P8 => PriNum::P9,
            PriNum::P9 => PriNum::P10,
            PriNum::P10 => unreachable!(),
        }
    }
    const a:PriNum=PriNum::P9;
    const BB: [PriNum;2] = [{a},next_pri(a)];
}

#[test]
pub fn test() {
    if f32::NAN == f32::NAN {
        println!("==> NaN == NaN");
    } else {
        println!("==> NaN != NaN");
    }

    // let s = "1万3百20";
    // let s = "-5 * ( ( -3 + 6 ) )";
    // let s = r"
    // 64
    // 10913
    // 290
    // 176
    // 946
    // 2333
    // avg
    // ";
    // let s = r"
    // 16 32
    // avg
    // ";
    // let s = "31 cnt& cnt";
    // let ss = s.to_string().as_str();
    let s = "fn f x=x \n f 1";
    let s = "fn f2 x = x*7 \n 2 f2& + 3 sum 4";
    let s = "3>4, not";
    // let s = "1900 2*";
    // let s = "\r";
    // let s = "sum 2 3 4";
    
    let s = s.chars().collect::<Box<[char]>>();
    let s = s.as_ref();
    // println!("====== {s:?}");
    // let a = &s[3];
    // let vv = parse_number(s);
    // let Some(vv) = parse_symbol(s) else {return};
    // let vv = skip_blank_back(s);
    // let vv = parse_fn(s);
    let vv = parse(s);
    println!("==={vv:?}");
}

fn parse_fn_exp(fn_def: Fndef, data:&[Et])->Option<Et> {
    let mut context = Context {
        frame_stack: Vec::<Frame>::new(),
        symbols: BTreeMap::new(),
        fn_codes: BTreeMap::new(),
    };
    context.frame_stack.push(Frame::new());

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
fn parse(src:&[char])->Option<Et> {
    let mut context = Context {
        frame_stack: Vec::<Frame>::new(),
        symbols: BTreeMap::new(),
        fn_codes: BTreeMap::new(),
    };
    context.frame_stack.push(Frame::new());

    let vv = parse_exp(&mut context, src);
    vv
}
#[derive(Clone, Copy)]
enum RetRule {
    None,
    Ignore,
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

        let Some((ut, src_rest)) = unit_next(src,frame_empty,&context.fn_codes) else {
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

            Ut::Op(Opi { act: Act::Aux(tag), prinum,.. },..) => {
                println!("++++> op Aux ({:?}) {:?}",tag, src_rest);
                src = src_rest;
                let retrule = if let ";" = tag {RetRule::None} else {RetRule::Ignore};
                Some((prinum,retrule))
            }

            Ut::Op(e,kind) => {
                if  frame.opi.last().is_none() ||
                    frame.opi.last().unwrap().0.prinum < e.prinum
                {
                    println!("++++> op : {:?} {:?}",e.name, src_rest);
                    src = src_rest;
                    push_action((e.clone(),kind), &mut frame.opi);
                    // 左目运算符，只和左边有关系，必须要执行
                    // 这个和有无返回值没有关系啦，统一了，;也统一了
                    if let DataWhere::Left(_) = e.data_where {
                        Some((e.prinum,RetRule::Ignore))
                    } else {
                        None
                    }
                } else {
                    Some((e.prinum,RetRule::Ignore))
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
                Some((PriNum::P0,RetRule::Ignore))
            }

            Ut::Sy(sym) => {
                src = src_rest;
                println!("++++> SYM {} {:?}", sym, src_rest);
                push_data(Data::Sym(sym), &mut frame.data);
                None
            }

            Ut::Fndef(fn_def) => {
                src = src_rest;
                println!("++++> CODE {:?} {:?}",fn_def, src_rest);
                push_code(fn_def,&mut context.fn_codes);
                None
            }

            // Ut::Fn(fn_name, kind) => {
            //     src = src_rest;
            //     println!("++++> fn {:?}",fn_name);

            //     None
            // }

            // Ut::Assign => {
            //     src = &src[1..];
            //     let frame_empty: Frame = Frame::new();
            //     frame_stack.push(frame_empty);
            //     frame = frame_stack.last_mut().unwrap();
            //     None
            // }

            Ut::End => {
                println!("==========> END {src:?}");
                Some((PriNum::P0,RetRule::Ignore))
            }
        };

        if let Some(cond) = r {
            try_pop_exp_util(&context.fn_codes,&mut context.symbols,frame, cond.clone());
            if cond.0 == PriNum::P0 && frame.opi.is_empty() {
                // assert_eq!(frame.data.len(),1);
                let mut vv = frame.data.last().cloned();
                if let Some(Data::Sym(ref d)) = vv {
                    // assure the value poped out must be val instead of sym
                    // ******
                    vv = Some(Data::Val(context.symbols[d]));
                }

                // let vv = value_of(&context.symbols, vv);
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
#[derive(PartialEq,Debug,Clone,Copy)]
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

fn skip_space_back(src:&[char])->(&[char],Option<char>) {
    let Some(p) = src.iter().rev().position(|e|*e!=' ') else {
        // 没有非空格
        return (&[],None);
    };
    assert!(p>=0);
    (&src[..src.len()-p],Some(src[src.len()-p-1]))
}

fn skip_blank_back(src:&[char])->(&[char],Option<char>) {
    let Some(p) = src.iter().rev().position(|e|!SKIP_CHARS.contains(e)) else {
        // 没有非空格
        return (&[],None);
    };
    assert!(p>=0);
    (&src[..src.len()-p],Some(src[src.len()-p-1]))
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

fn parse_fn(src:&[char])->Option<(&[char],Vec<&[char]>,&[char],&[char])> {
    // const END_CHARS: [char; 2] = ['\r','\n'];

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

    // body
    let src = &src[1..];

    let (src,Some(c0)) = skip_blank(src) else {
        assert!(src.is_empty());
        return Some((name, ps, src, src));
    };

    // println!("[{c0}]  {src:?}");

    let mut bracket_cnt = 0;
    let mut last_c = None;
    let is_first_bracket = c0=='(';

    let mut index_next = 0;
    for c in src {
        index_next += 1;
        match c {
            '(' =>
                bracket_cnt+=1,
            ')' => {
                bracket_cnt-=1;
                if bracket_cnt == 0 && is_first_bracket {
                    last_c = Some(c);
                    break;
                }
                if bracket_cnt<0 {
                    return None;
                }
            }
            '\r'|'\n' => 
                if bracket_cnt == 0 {
                    last_c = Some(c);
                    break;
                }
            _ => (),
        }
    }

    if last_c.is_none() && !is_first_bracket {
        let body = &src[..index_next];
        let rest = &src[index_next..];
        let (body,_char) = skip_space_back(body);
        return Some((name,ps,body,rest));
    }

    let Some(last_c) = last_c else {
        return None;
    };

    if is_first_bracket && *last_c != ')' {
        return None;
    }
    
    let indent_cnt = is_first_bracket as usize;
    let body_start = indent_cnt;
    let body_end = index_next-indent_cnt;
    let body = &src[body_start..body_end];
    let rest = &src[body_end..];

    let (body,_) = skip_blank(body);
    let (body,_) = skip_blank_back(body);

    Some((name, ps, body, rest))
}

#[derive(Clone, Copy,Debug,Eq,PartialEq, Ord,PartialOrd)]
enum Et {
    // Bool(bool),
    I32(i32),
    // Real(f32)
}
type SymbolMap = BTreeMap<String,Et>;

impl Et {
    fn as_i32(&self)->&i32 {
        let Et::I32(v) = self else {
            panic!("the type is not supported");
        };
        v
    }
}

#[derive(Clone)]
enum Act {
    Aux(&'static str),

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
    fn call_aux(&self,_d:&[Data]) {
    }
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
#[derive(Clone)]
enum Pri {
    LBracket,
    RBracket,
}
const PRI_UT: [(char, Ut); 2] = [
    ('(', Ut::Pr(Pri::LBracket)),
    (')', Ut::Pr(Pri::RBracket))
];

#[derive(Clone, Copy,Debug)]
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
    Fndef(Fndef),
    // Fn(String,Para),
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
    P0, // )
    P1, // = ;
    P2, // + -
    P3, // * /
    P4, // (
    P5,
    P6,
    P7,
    P8,
    P9,
    P10
}

#[derive(Clone, Copy, Debug)]
enum Ret {
    Value,
    None,
}

#[derive(Clone,Debug)]
enum Sym {
    Str(&'static[char]),
    String(String),
}

#[derive(Clone)]
struct Opi {
    name: Sym,//&'static[char],
    act: Act,
    prinum: PriNum,
    data_where: DataWhere,
    ret: Ret,
    pred: char, // data
}
impl Opi {
    const fn new(name:Sym, act:Act, prinum: PriNum, data_where:DataWhere, ret:Ret)->Self {
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
    let v2 = *d[0].as_et();
    let _old = match &d[1] {
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

fn op_cnt (symbol:&mut BTreeMap<String,Et>,data:&[Data])->Et {
    Et::I32(data.len() as i32)
}

fn op_avg (symbol:&mut BTreeMap<String,Et>,data:&[Data])->Et {
    let Et::I32(sum) = op_sum(symbol,data) else {
        panic!("not supports non i32");
    };
    let n = data.len() as i32;
    Et::I32(sum/n)
}

fn op_fn_def(src:&[char])->Option<(&[char],&[char])> {
    let Some((_name,ref _ps,body, rest)) = parse_fn(src) else {
        return None;
    };
    Some((body, rest))
}

fn op_fn_do(fn_name:&str,codes:&FnCodeMap,symbol:&BTreeMap<String,Et>,data:&[Data])->Et {
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
    let v1 = value_of(symbol, &d[1]);
    let v2 = value_of(symbol, &d[0]);
    Et::I32((v1 > v2) as i32)
}
fn op_ge (symbol:&BTreeMap<String,Et>,d:&[Data])->Et {
    let v1 = value_of(symbol, &d[1]);
    let v2 = value_of(symbol, &d[0]);
    Et::I32((v1 >= v2) as i32)
}
fn op_lt (symbol:&BTreeMap<String,Et>,d:&[Data])->Et {
    let v1 = value_of(symbol, &d[1]);
    let v2 = value_of(symbol, &d[0]);
    Et::I32((v1 < v2) as i32)
}
fn op_le (symbol:&BTreeMap<String,Et>,d:&[Data])->Et {
    let v1 = value_of(symbol, &d[1]);
    let v2 = value_of(symbol, &d[0]);
    Et::I32((v1 <= v2) as i32)
}
fn op_eq (symbol:&BTreeMap<String,Et>,d:&[Data])->Et {
    let v1 = value_of(symbol, &d[1]);
    let v2 = value_of(symbol, &d[0]);
    Et::I32((v1 == v2) as i32)
}
fn op_ne (symbol:&BTreeMap<String,Et>,d:&[Data])->Et {
    let v1 = value_of(symbol, &d[1]);
    let v2 = value_of(symbol, &d[0]);
    Et::I32((v1 != v2) as i32)
}
fn op_cmp (symbol:&BTreeMap<String,Et>,d:&[Data])->Et {
    let v1 = value_of(symbol, &d[1]);
    let v2 = value_of(symbol, &d[0]);
    Et::I32((v1.partial_cmp(&v2).unwrap()) as i32)
}
fn op_and (symbol:&BTreeMap<String,Et>,d:&[Data])->Et {
    let v1 = value_of(symbol, &d[1]);
    let v2 = value_of(symbol, &d[0]);
    Et::I32((v1.as_bool() && v2.as_bool()) as i32)
}
fn op_or (symbol:&BTreeMap<String,Et>,d:&[Data])->Et {
    let v1 = value_of(symbol, &d[1]);
    let v2 = value_of(symbol, &d[0]);
    Et::I32((v1.as_bool() || v2.as_bool()) as i32)
}
fn op_not (symbol:&BTreeMap<String,Et>,d:&[Data])->Et {
    let v1 = value_of(symbol, &d[0]);
    Et::I32((!v1.as_bool()) as i32)
}

// 如何初始化这个，的确得想想，Lazystatic好呀，不用锁，最长匹配优先
const OPS:[Opi;20] = [
    Opi::new(Sym::Str(&[',']),Act::Aux(","),PriNum::P1,DataWhere::Zero,Ret::None),
    Opi::new(Sym::Str(&[';']),Act::Aux(";"),PriNum::P1,DataWhere::Zero,Ret::None),

    Opi::new(Sym::Str(&['=','=']),Act::Eq(op_eq),PriNum::P6,DataWhere::Any(2),Ret::Value),
    Opi::new(Sym::Str(&['=']),Act::Ass(op_assign),PriNum::P2,DataWhere::Any(2),Ret::Value),

    Opi::new(Sym::Str(&['o','r']),Act::Or(op_or),PriNum::P3,DataWhere::Any(2),Ret::Value),

    Opi::new(Sym::Str(&['a','n','d']),Act::And(op_and),PriNum::P4,DataWhere::Any(2),Ret::Value),

    Opi::new(Sym::Str(&['>','=']),Act::Ge(op_ge),PriNum::P5,DataWhere::Any(2),Ret::Value),
    Opi::new(Sym::Str(&['>']),Act::Gt(op_gt),PriNum::P5,DataWhere::Any(2),Ret::Value),
    Opi::new(Sym::Str(&['<','=']),Act::Le(op_le),PriNum::P5,DataWhere::Any(2),Ret::Value),
    Opi::new(Sym::Str(&['<']),Act::Lt(op_lt),PriNum::P5,DataWhere::Any(2),Ret::Value),

    Opi::new(Sym::Str(&['!','=']),Act::Ne(op_ne),PriNum::P6,DataWhere::Any(2),Ret::Value),
    // Opi::new(Sym::Str(&['=','=']),Act::Eq(eq),PriNum::P6,DataWhere::Any(2),Ret::Value),
    Opi::new(Sym::Str(&['c','m','p']),Act::Cmp(op_cmp),PriNum::P6,DataWhere::Any(2),Ret::Value),

    Opi::new(Sym::Str(&['s','u','m']),Act::Opfn(op_sum),PriNum::P7,DataWhere::Any(-1),Ret::Value),
    Opi::new(Sym::Str(&['a','v','g']),Act::Opfn(op_avg),PriNum::P7,DataWhere::Any(-1),Ret::Value),

    Opi::new(Sym::Str(&['+']),Act::Add(op_add),PriNum::P8,DataWhere::Any(2),Ret::Value),
    Opi::new(Sym::Str(&['-']),Act::Sub(op_sub),PriNum::P8,DataWhere::Any(2),Ret::Value),

    Opi::new(Sym::Str(&['*']),Act::Mul(op_mul),PriNum::P9,DataWhere::Any(2),Ret::Value),
    Opi::new(Sym::Str(&['/']),Act::Div(op_div),PriNum::P9,DataWhere::Any(2),Ret::Value),

    Opi::new(Sym::Str(&['n','o','t']),Act::Not(op_not),PriNum::P10,DataWhere::Any(1),Ret::Value),
    Opi::new(Sym::Str(&['c','n','t']),Act::Opfn(op_cnt),PriNum::P10,DataWhere::Any(-1),Ret::Value),
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

mod con {
    use std::cmp::Ordering;
    use super::{Opi,Sym};
    
    const fn max(ops:&[Opi])->usize {
        let n:usize = ops.len();
        assert!(n>=2);
        let mut m = &ops[0];
        let mut ii = 0;
        let mut i = 1;
        loop {
            let Sym::Str(n1) = m.name else {unreachable!()};
            let op = if i<n {i+=1;&ops[i]} else {break;};
            let Sym::Str(n2) = op.name else {unreachable!()};
            let r = cmp_str(n1,n2);
            if r.is_le() {
                m = op;
                ii = i;
            }
        }
        return ii;
    }

    const fn cmp_str(a1:&[char],a2:&[char])->Ordering {
        let n1:usize = a1.len();
        let n2:usize = a2.len();
        let mut i1 = 0;
        let mut i2 = 0;
        loop {
            let c1 = if i1<n1 {Some(a1[i1])} else {None};
            let c2 = if i2<n2 {Some(a2[i2])} else {None};
            match (c1,c2) {
                (None, None) => break Ordering::Equal,
                (None, Some(_)) => break Ordering::Less,
                (Some(_), None) => break Ordering::Greater,
                (Some(c1), Some(c2)) =>
                    if c1 == c2 { i1+=1;i2+=1; }
                    else if c1 > c2 {break Ordering::Greater}
                    else {break Ordering::Less}
            }
        }
    }
}
//     const fn max (ops:&[Opi])-> &Opi {
//         ops.b
//         let x = &ops[0];
//         // let x = &x.name;
//         let Sym::Str(x) = &ops[0].name else {unreachable!()};
//         let max = ops.first();
//         // for e in ops {
            
//         // }
//         // ops.sort()
//         enum EEE {a(&'static str),b(String)};
//         let aa = EEE::a("");
//         let EEE::b(a) = aa else {unimplemented!()};
//         // a.push('a');
//         &ops[0]
//     }
//     let aa = std::sync::LazyLock::new(||{
//         let mut ops = ops;
//         ops.sort_by(|
//             op1,//Opi{name:Sym::Str(name1),..},
//             op2,//Opi{name:Sym::Str(name2),..}
//             |
//             // let Opi{name:Sym::Str(name1),..} = op1 else {unreachable!();};
//             let Sym::Str(a) = op1.name else {unreachable!()};
//             name1.cmp(name2)
//         );
//         ops
//     });
//     let aa = &*aa;
//     let aa = aa.clone();
//     aa
// };

// }

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

const SKIP_CHARS:[char;3] = [' ','\r','\n'];

struct Unit<'a> {
    ut: Ut,
    src_next: &'a[char],
}

impl Sym {
    fn as_static_slice(&self)->&'static[char] {
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
fn unit_next<'a>(src:&'a[char], frame_empty:bool,codes:&FnCodeMap)->Option<(Ut,&'a[char])> {
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
            println!("number parsed is {ni}+({}==={_deci}/{_w})", _deci as f32/_w as f32);
            return Some((Ut::Ni(Et::I32(ni)),src_rest));
        }
    // <2> +-*/=;sum cnt
    } if let Some(op) = OPS.iter().find(|e|src.starts_with(e.name.as_static_slice())) {
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
    // <4|5|6> symbol | fndef | fn
    } else if UPPER_CHARS.contains(c) || LOWER_CHARS.contains(c) {
        if let Some((sym,src_rest)) = parse_symbol(src) {
            // <5> fn def
            if let ['f','n'] = sym {
                let Some((name,ps,body,src_rest)) = parse_fn(src) else {
                    return None;
                };
                let name = name.iter().collect::<String>();
                let ps = ps.iter().map(|e|e.iter().collect::<String>()).collect();
                let body = body.to_vec();
                let fn_def = Fndef {name,ps,body};
                return Some((Ut::Fndef(fn_def),src_rest));
            }

            let sym = sym.iter().collect::<String>();
            let fn_def = codes.get(&sym);

            // <4> symbol
            let Some(fn_def) = fn_def else {
                return Some((Ut::Sy(sym),src_rest));
            };

            // <6> fn
            let kind = if let Some('&') = src_rest.first() {
                (Para::Ref,1)
            } else {
                (Para::Consumed,0)
            };
            let fn_name = Sym::String(sym);
            let fn_dw = DataWhere::Any(fn_def.ps.len() as i32);
            const FN_PRINUM: PriNum = PriNum::P10;
            const FN_DO: Act = Act::Fn(op_fn_do);
            const FN_RET: Ret = Ret::Value;
            let fn_opi = Opi::new(fn_name, FN_DO, FN_PRINUM, fn_dw, FN_RET);
            return Some((Ut::Op(fn_opi, kind.0),&src_rest[kind.1..]));
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
fn push_code(fn_def:Fndef, codes:&mut FnCodeMap) {
    codes.insert(fn_def.name.clone(), fn_def);
}

fn try_pop_exp_util(codes:&FnCodeMap,symbol:&mut SymbolMap,frame: &mut Frame, cond:(PriNum,RetRule)) {
    let (prinum,lastret) = cond;
    while let Some((last_op,_last_para)) = frame.opi.last() {
        if last_op.prinum >= prinum {
            let is_op_last = frame.opi.len()==1;
            let ret = if let (RetRule::None,true) = (&lastret,is_op_last)
                {RetRule::None} else {RetRule::Ignore}; 
            pop_exp(codes,symbol,frame,ret);
        } else {
            break;
        }
    }
}
fn pop_exp(codes:&FnCodeMap,symbol:&mut SymbolMap,frame: &mut Frame, ret:RetRule)->Option<()> {
    let Some(opi) = frame.opi.pop() else {
        return None;
    };
    println!("\t~~~~~~~ acton:{:?} ~~~~~~~>", opi.0.name);
    println!("\t0:{:?}",frame.data);
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
        Act::Aux(_) => {
            d3 = None;
            println!("      {:?}({d:?})",opi.0.name);
            unreachable!("the code would not be runed here");
        }
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
    if let (Ret::Value,RetRule::Ignore) = (opi.0.ret,ret) {
        if let Some(d3) = d3 {
            frame.data.push(Data::Val(d3));
        }
    }

    println!("\t~~~~~~~~ 6:{:?}",frame.data);
    Some(())
}

#[derive(Clone,Debug)]
struct Fndef {
    name: String,
    ps: Vec<String>,
    body: Vec<char>,
}
type FnCodeMap = BTreeMap<String,Fndef>;
struct Context {
    frame_stack: Vec<Frame>,
    symbols: SymbolMap,
    fn_codes: FnCodeMap
}


