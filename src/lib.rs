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
    // avg
    // ";
    // let s = r"
    // 16 32
    // avg
    // ";
    // let s = "31 cnt& cnt";
    // let ss = s.to_string().as_str();
    // let s = "fn f x=x*(2+3)*x , f 1";
    // let s = "fn f2 x = x*7, 2 f2& + 3 sum 4";
    // let s = "57/12";
    // let s = "1900 2*";
    // let s = "sum 2 3 4";
    // let s = "\r";
    // let s = "3+5*2";
    // let s = "if 0 else 9 end";
    // let s = "if 1 then if 1 else 22 end elif 3 then 4 else 5 end";
    let s = "i=1; while i<2 {i=i+1}";
    
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
fn parse(src:&[char])->Option<Et> {
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
#[derive(Debug,Clone, Copy)]
enum RetRule {
    None,
    Ignore,
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

    fn print_src(src:&[char],sign_number:bool) {
        print!("---------------------------------------------------");
        println!(" : [{sign_number}] {}",String::from_iter(src));
    }
    fn print_token(token:&Token) {
        if let Token::Op(op,para) = &token {
            println!("token: {:?}", (&op.name,&op.act,para));
        } else {
            println!("token: {token:?}");
        };
    }
    fn print_corre(corre:&CorreE, correspond:&CorrespondVec) {
        if let CorreE::Op(Opi{name,..}, _)= corre {
            println!("corre: {:?}\t\t{:?}", name,correspond);
        } else {
            println!("corre: {:?}\t\t{:?}", corre,correspond);
        }
    }
    fn print_structure(subject_matter:&PopSubjectMatter,cond_stack:&CondStack,frame:&Frame) {
        println!("structure: {:?}\t\t{:?}",subject_matter,cond_stack);
        println!("\t\t\tdata: {:?}",frame.data);
    }

    let exit_value = loop {
        // let frame = frame_stack.last_mut().unwrap();
        // let frame_empty = frame.data.is_empty() && frame.opi.is_empty();
        print_src(src,sign_number);
        let Some((token, src_rest)) = token_next(src,sign_number,&context.fn_codes) else {
            return None; // error
        };
        print_token(&token);
        if sign_number {
            // here, if we get any token of data or op, means the position is not at the first, 
            // the +/- flag is RESET to false
            if let Token::Data(..)|Token::Op(..) = token {
                sign_number = false;
            }
        }
        let Some(corre) = ast_correspond(token, whole, src_rest, &mut context.correspond, &mut context.fn_codes) else {
            return None; // error
        };
        print_corre(&corre,&context.correspond);
        if context.correspond.exp_start && !sign_number {
            sign_number = true;
        }
        src = src_rest;
        if let CorreE::IgnoreNextSteps = corre {
            continue;
        }
        let corre_size = context.correspond.len();
        let ptr = cond_stack as *const CondStack;
        let subject_matter= push_exp(corre, corre_size, frame_stack, cond_stack);
        unsafe {
            let stack = std::mem::transmute::<*const CondStack, &CondStack>(ptr);
            print_structure(&subject_matter,stack,frame_stack.last_mut().unwrap());
        }
        if let PopSubjectMatter::Donot = subject_matter {
            continue;
        }
        let frame = frame_stack.last_mut().unwrap();
        if let PopSubjectMatter::PrAgain(_,_,stacksize,offset) = subject_matter {
            println!("<<<<<<<<<<<< src again back to: {offset}, stacksize: {stacksize}");
            src = src_again(whole, stacksize,offset,&mut context.correspond);
        }
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

#[cfg(never)]
fn parse_exp(context: &mut Context, src: &[char], just_grammer:bool)->Option<Et> {
    let frame_stack = &mut context.frame_stack;

    if src.is_empty() {
        return None;
    }
    let mut src = src;

    println!("src: {src:?}");
    
    let rr = loop {
        let mut frame = frame_stack.last_mut().unwrap();
        let frame_empty = frame.data.is_empty() && frame.opi.is_empty();

        let Some((ut, src_rest)) = token_next(src,frame_empty,&context.fn_codes) else {
            // error
            return None;
        };

        let r = match ut {
            Token::Data(data) => {
                println!("++++>data: {:?} {:?}",data, src_rest);
                src = src_rest;
                if just_grammer {continue;}
                push_data(data, &mut frame.data);
                None
            }

            Token::Op(Opi { act: Act::Aux(tag), prinum,.. },..) => {
                println!("++++> op Aux ({:?}) {:?}",tag, src_rest);
                src = src_rest;
                let retrule = if let ";" = tag {RetRule::None} else {RetRule::Ignore};
                Some((prinum,retrule))
            }

            Token::Op(e,kind) => {
                if  frame.opi.last().is_none() ||
                    frame.opi.last().unwrap().0.prinum < e.prinum
                {
                    println!("++++> op : {:?} {:?}",e.name, src_rest);
                    src = src_rest;
                    if just_grammer { continue; }
                    push_action((e.clone(),kind), &mut frame.opi);
                    // 左目运算符，只和左边有关系，必须要执行
                    // 这个和有无返回值没有关系啦，统一了，;也统一了
                    // 本来是和左目和；运算符通用化的，后来；被辅助化以后或者说关键字话以后，基本就没用了
                    // 除非有左目运算，要立即参与运算的，所以就返回了Some，要执行
                    if let DataWhere::Left(_) = e.data_where {
                        Some((e.prinum,RetRule::Ignore))
                    } else {
                        None
                    }
                } else {
                    Some((e.prinum,RetRule::Ignore))
                }
            }

            Token::Corr(CorreE::Sub(Bracket::LRound)) => {
                src = src_rest;
                println!("====> {:?}",src);
                if just_grammer {continue;}
                let frame_empty: Frame = Frame::new();
                frame_stack.push(frame_empty);
                frame = frame_stack.last_mut().unwrap();
                None
            }

            Token::Corr(CorreE::Sub(Bracket::RRound)) => {
                src = src_rest;
                println!("=====> ****** {src:?}");
                Some((PriNum::P0,RetRule::Ignore))
            }

            Token::Fndecl(fn_def) => {
                src = src_rest;
                println!("++++> CODE {:?} {:?}",fn_def, src_rest);
                if just_grammer {continue;}
                push_fndef(fn_def,&mut context.fn_codes);
                None
            }

            Token::Corr(CorreE::End) => {
                println!("==========> END {src:?}");
                Some((PriNum::P0,RetRule::Ignore))
            }
        };
        if just_grammer {continue;}


        // enum Bound {
        //     Begin,
        //     End
        // }
        // enum RunEle {
        //     Data(Data),
        //     Op(Opi),
        //     Subexp(Bound),
        // }
        // fn exp_env(context:&mut Context,re:RunEle) {
        //     fn top(context: &mut Context)->&mut Frame {
                
        //     }
        //     match re {
        //         Data => {
        //             push_data(Data::Val(et), &mut frame.data);
        //         }
        //     }
        // }

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

// fn parse_then_else(iff:bool,src:&[char])->Option<(&[char],&[char])> {
//     let (src,Some(c)) = skip_blank(src) else {
//         // finished normally
//         return Some((&[],&[]));
//     };
//     match (iff,src) {
//         (true,['t','h','e','n',c,..]) if !is_char(*c) => {
//             unimplemented!("call parse exp")
//         }
//         (true,['e','l','s','e',c,..]) if !is_char(*c) => {
//             unimplemented!("just parse grammer")
//         }
//         (false,['t','h','e','n',c,..]) if !is_char(*c) => {
//             unimplemented!("call parse exp")
//         }
//         (false,['e','l','s','e',c,..]) if !is_char(*c) => {
//             unimplemented!("call parse grammer")
//         }
//         _ => {return None;} // error
//     }
//     None
// }

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

fn parse_fn_decl(src:&[char])->Option<(&[char],Vec<&[char]>,&[char])> {
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

    // name param is ok, body reserved for parse by gammer
    return Some((name, ps, &src[1..]));
}

#[cfg(never)]
fn parse_fn_def(src:&[char])->Option<(&[char],Vec<&[char]>,&[char],&[char])> {
//     // const END_CHARS: [char; 2] = ['\r','\n'];

//     let (src,_char_next) = skip_blank(src);

//     // 如果不是fn 返回出错
//     if !src.starts_with(&['f','n']) {
//         return None;
//     }
//     let src = &src[2..];


//     let Some((name,rest)) = parse_symbol(src) else {
//         return None;
//     };
//     let mut src = rest;

//     let mut ps = vec![];
//     while let Some((p,rest)) = parse_symbol(src) {
//         // let sym = sym.iter().collect::<String>();
//         ps.push(p);
//         src = rest;
//     }

//     let (src, Some('=')) = skip_blank(src) else {
//         return None;
//     };

//     // body
//     let src = &src[1..];

//     let (src,Some(c0)) = skip_blank(src) else {
//         assert!(src.is_empty());
//         return Some((name, ps, src, src));
//     };

//     // println!("[{c0}]  {src:?}");

//     let mut bracket_cnt = 0;
//     let mut last_c = None;
//     let is_first_bracket = c0=='(';

//     let mut index_next = 0;
//     for c in src {
//         index_next += 1;
//         match c {
//             '(' =>
//                 bracket_cnt+=1,
//             ')' => {
//                 bracket_cnt-=1;
//                 if bracket_cnt == 0 && is_first_bracket {
//                     last_c = Some(c);
//                     break;
//                 }
//                 if bracket_cnt<0 {
//                     return None;
//                 }
//             }
//             '\r'|'\n' => 
//                 if bracket_cnt == 0 {
//                     last_c = Some(c);
//                     break;
//                 }
//             _ => (),
//         }
//     }

//     if last_c.is_none() && !is_first_bracket {
//         let body = &src[..index_next];
//         let rest = &src[index_next..];
//         let (body,_char) = skip_space_back(body);
//         return Some((name,ps,body,rest));
//     }

//     let Some(last_c) = last_c else {
//         return None;
//     };

//     if is_first_bracket && *last_c != ')' {
//         return None;
//     }
    
//     let indent_cnt = is_first_bracket as usize;
//     let body_start = indent_cnt;
//     let body_end = index_next-indent_cnt;
//     let body = &src[body_start..body_end];
//     let rest = &src[body_end..];

//     let (body,_) = skip_blank(body);
//     let (body,_) = skip_blank_back(body);

//     Some((name, ps, body, rest))
    None // for avoiding error
}

#[derive(Clone, Copy,Debug,Eq,PartialEq, Ord,PartialOrd)]
enum Et {
    // Bool(bool),
    I32(i32),
    // Real(f32)
}
type SymbolMap = BTreeMap<String,Et>;
type FrameVec = Vec<Frame>;

impl Et {
    fn as_i32(&self)->&i32 {
        let Et::I32(v) = self else {
            panic!("the type is not supported");
        };
        v
    }
}

#[derive(Clone,Debug)]
enum Act {
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

#[derive(Clone,Copy,Debug)]
enum Bracket {
    LRound,
    RRound,
    // LCurly,
    // RCurly,
}
impl Bracket {
    const METAS: [(Token,char,PriNum); 2] = [
        (Token::Pr(Bracket::LRound), '(', PriNum::P12),
        (Token::Pr(Bracket::RRound), ')', PriNum::P1),
        // (Token::Pr(Bracket::LCurly), '{', PriNum::P12),
        // (Token::Pr(Bracket::RCurly), '}', PriNum::P1),
    ];
    const fn info(&self)->&(Token,char,PriNum) {
        &Self::METAS[*self as usize]
    }
    const fn prinum(&self)->PriNum {
        self.info().2
    }
}

#[derive(Clone,Copy,Debug)]
enum Curly {
    LCurly,
    RCurly,
}
impl Curly {
    const METAS: [(Token,char,PriNum); 2] = [
        (Token::Curly(Curly::LCurly), '{', PriNum::P12),
        (Token::Curly(Curly::RCurly), '}', PriNum::P1),
    ];
    const fn info(&self)->&(Token,char,PriNum) {
        &Self::METAS[*self as usize]
    }
    const fn prinum(&self)->PriNum {
        self.info().2
    }
}


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

#[derive(Clone, Copy,Debug)]
enum Para {
    Consumed,
    Ref,
}
type Sstr = &'static str;
type Schars = &'static[char];
#[derive(Clone, Copy,Debug)]
enum Keyword
{
    If,Then,Elif,Else,Fn,End,While,Continue,Break,
}
struct KeywordMeta {
    id: Keyword,
    name: Schars,
}
impl KeywordMeta {
    const fn new(id:Keyword,name:Schars)->Self {
        KeywordMeta {id,name}
    }
}
impl ToChars for KeywordMeta {
    fn to_chars(&self)->&[char] {
        self.name
    }
}
impl ToChars for &KeywordMeta {
    fn to_chars(&self)->&[char] {
        self.name
    }
}
impl Keyword {
    const METAS: [KeywordMeta; 9] = [
        KeywordMeta::new(Keyword::If,&['i','f']),
        KeywordMeta::new(Keyword::Then,&['t','h','e','n']),
        KeywordMeta::new(Keyword::Elif,&['e','l','i','f']),
        KeywordMeta::new(Keyword::Else,&['e','l','s','e']),
        KeywordMeta::new(Keyword::Fn,&['f','n']),
        KeywordMeta::new(Keyword::End,&['e','n','d']),
        KeywordMeta::new(Keyword::While,&['w','h','i','l','e']),
        KeywordMeta::new(Keyword::Continue,&['c','o','n','t','i','n','u','e']),
        KeywordMeta::new(Keyword::Break,&['b','r','e','a','k']),
        ];
    const BEGIN_PRINUM:PriNum = PriNum::P12; // actually, we never will be used
    const END_PRINUM:PriNum = PriNum::P1;
    const fn info(&self)->&'static KeywordMeta {
        let i = *self as usize;
        &Self::METAS[i]
    }
    const fn name(&self)->Schars {
        let i = *self as usize;
        Self::METAS[i].name
    }
    const fn all()->&'static[KeywordMeta] {
        Self::METAS.as_slice()
    }
    fn iter() -> std::slice::Iter<'static, KeywordMeta> {
        Self::METAS.iter()
    }
}

fn ff_test() {
    let kwi = Keyword::If.info();
    let mut aa = Keyword::all().match_starts(&[],None);
}

trait ToChars {
    fn to_chars(&self)->&[char];
}

trait MatchStart<Item:ToChars> {
    fn match_starts<'a>(&self,main:&'a[char],char_test:Option<CharTest>)
    ->(Option<&Item>,&'a[char]);
}

// how to implement for [T]
trait MatchStartTest {
    fn match_starts<'a,Item>(&self,main:&'a[char],char_test:Option<CharTest>)
    ->(Option<&Item>,&'a[char]);
}
impl<const N:usize,T:ToChars> MatchStart<T> for [T;N] {
    fn match_starts<'a>(&self,main:&'a[char],char_test:Option<CharTest>)
    ->(Option<&T>,&'a[char]) {
        self.as_slice().match_starts(main, char_test)
    }
}
impl<T:ToChars> MatchStart<T> for [T]  {
    fn match_starts<'a>(&self,main:&'a[char],char_test:Option<CharTest>)
    ->(Option<&T>,&'a[char]) {
        let Some(t) = self.iter().find(|e|
            main.starts_with(e.to_chars())
        ) else {
            return (None,main);
        };
        // here, match the prefixed
        // let len = t.to_chars().len();
        let rest = &main[t.to_chars().len()..];
    
        // no test-char, return true
        let Some(char_test) = char_test else {
            return (Some(t),rest);
        };
        // if main is no more return true
        let Some(c) = rest.first() else {
            assert!(rest.is_empty());
            return (Some(t),rest);
        };
        // test the next char
        if char_test(*c) { (Some(t),rest) } else {(None,main)}
    }
}

// // trait MatchStarts<Item> :Iterator<Item:ToChars> {
// trait MatchStarts<Item:ToChars> :Iterator<Item=Item> {
//         fn match_starts<'a>(&mut self,main:&'a[char],char_test:Option<CharTest>)
//     ->(Option<Self::Item>,&'a[char]) where Self:Sized{
// trait MatchStarts<Item:ToChars> {
//     fn match_starts<'a>(&mut self,main:&'a[char],char_test:Option<CharTest>)
//     ->(Option<Item>,&'a[char])
//     where Self:Sized+Iterator<Item=Item> {
//         let Some(t) = self.find(|e|
//             main.starts_with(e.to_chars())
//         ) else {
//             return (None,main);
//         };
//         // here, match the prefixed
//         let rest = &main[t.to_chars().len()..];
    
//         // no test-char, return true
//         let Some(char_test) = char_test else {
//             return (Some(t),rest);
//         };
//         // if main is no more return true
//         let Some(c) = main.get(t.to_chars().len()) else {
//             assert!(rest.is_empty());
//             return (Some(t),rest);
//         };
//         // test the next char
//         if char_test(*c) { (Some(t),rest) } else {(None,main)}
//     }
// }
// impl<E:ToChars,T:Iterator<Item=E>> MatchStarts<E> for T where {}

// end of sub programm
// #[derive(Debug,Clone, Copy)]
// struct End;
// impl End {
//     const PRINUM:PriNum = PriNum::P1;
// }

// end of progamm
#[derive(Debug,Clone, Copy)]
struct Exit;
impl Exit {
    const PRINUM:PriNum = PriNum::P0;
}
// 后面考虑加入啥（数据是引用，这样能减轻数据的传递）
#[derive(Debug,Clone)]
enum Token {
    Data(Data),
    Aux(Aux),
    Op(Opi,Para),
    Pr(Bracket),
    Curly(Curly),
    Fndecl(String,Vec<String>),
    Kw(Keyword),
    // End(End),
    Exit(Exit),
}

#[derive(Debug,Clone,PartialEq)]
enum DataWhere {
    Zero,
    Any(i32),
    Left(i32),
    Right(i32),
    Both(i32,i32),
    Mid(i32),
}

#[derive(Debug,Clone,Copy,PartialEq, PartialOrd)]
enum PriNum {
    // P0: exit; P1: pop frame; P2: minimum action num
    P0, P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, P11, P12
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
#[derive(Debug,Clone, Copy)]
enum Aux {
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
struct Auxi {
    id: Aux,
    name: char,
    prinum: PriNum,
    retrule: RetRule,
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
    const fn info(&self)->&'static Auxi {
        &Self::METAS[*self as usize]
    }
    /*const*/ fn match_starts(main:&[char])->(Option<&'static Auxi>,&[char]) {
        match main.first() {
            Some(AuxComma!()) => (Some(&Self::METAS[0]),&main[1..]),
            Some(AuxSemiColon!()) => (Some(&Self::METAS[1]),&main[1..]),
            _ => (None, main),
        }
    }
}
#[derive(Debug,Clone)]
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
const OPS:[Opi;18] = [
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
    // condition: Option<bool>,
    data: Vec<Data>,
    opi: Vec<(Opi,Para)>
}

impl Frame {
    fn new() -> Self {
        Self {/*condition:None,*/data:Vec::new(),opi:Vec::new()}
    }
}

macro_rules! DIGITS { () => {'0'..='9'}; }
macro_rules! LOWER_CHARS { () => {'a'..='z'}; }
macro_rules! UPPER_CHARS { () => {'A'..='Z'}; }

const DIGITS: std::ops::RangeInclusive<char> = DIGITS!();
const LOWER_CHARS: std::ops::RangeInclusive<char> = LOWER_CHARS!();
const UPPER_CHARS: std::ops::RangeInclusive<char> = UPPER_CHARS!();
const fn is_char(c:char)-> bool {
    match c {
        LOWER_CHARS!() | UPPER_CHARS!() => true,
        _ => false,
    }
}
const fn is_char_or_digit(c:char)->bool {
    match c {
        LOWER_CHARS!() | UPPER_CHARS!() | DIGITS!() => true,
        _ => false,
    }
}
const fn not_char_and_digit(c:char)->bool {
    !is_char_or_digit(c)
}
const fn is_blank_or_lcurly(c:char)->bool {
    match c {
        ' '|'\t'|'\r'|'\n'|'{' => true,
        _ => false,
    }
}

const SKIP_CHARS:[char;4] = [' ','\t','\r','\n'];

// struct Unit<'a> {
//     ut: Token,
//     src_next: &'a[char],
// }

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

type CharTest = fn(char)->bool;
fn match_starts<'a,'b,T:ToChars>(main:&'a[char],many_chars:&'b[T],char_test:Option<CharTest>)->(Option<&'b T>,&'a[char]) {
    // match the started prefix
    let Some(t) = many_chars.iter().find(|e|
        main.starts_with(e.to_chars())
    ) else {
        return (None,main);
    };
    // here, match the prefixed
    let rest = &main[t.to_chars().len()..];

    // no test-char, return true
    let Some(char_test) = char_test else {
        return (Some(t),rest);
    };
    // if main is no more return true
    let Some(c) = main.get(t.to_chars().len()) else {
        assert!(rest.is_empty());
        return (Some(t),rest);
    };
    // test the next char
    if char_test(*c) { (Some(t),rest) } else {(None,main)}
}

fn starts_with_and<'a>(main:&'a[char],sub:&[char],char_test:Option<CharTest>)->(bool,&'a[char]) {
    if main.starts_with(sub) {
        let Some(char_test) = char_test else {
            return (true,&main[sub.len()..]);
        };
        let Some(c) = main.get(sub.len()) else {
            return (true,&[]);
        };
        return (char_test(*c),&main[sub.len()..]);
    }
    return (false,main);
}
fn test_next_token_else(src:&[char])->(bool,&[char]) {
    let (src_next,_char_next) = skip_blank(src);
    // the next char cond equaliverlent to parse_symbol
    starts_with_and(src_next, Keyword::Else.name(), Some(not_char_and_digit))
}
const fn is_sym_start(c:&char)->bool {
    match c {
        UPPER_CHARS!() => true,
        LOWER_CHARS!() => true,
        _ => false,
    }
    // UPPER_CHARS.contains(&c) || LOWER_CHARS.contains(&c)
}
fn token_next<'a>(src:&'a[char], sign_number:bool, codes:&FnCodeMap)->Option<(Token,&'a[char])> {
    // skip ignored char
    let (src,Some(ref c)) = skip_blank(src) else {
        return Some((Token::Exit(Exit),src));
    };

    // 处理 开始的正负号，先不以单目运算符进行解析
    // the first + - maybe is number if next char is in 0-9
    if sign_number {
        if let '+'|'-' = c {
            if let Some(DIGITS!()) = src.get(1) {
                if let Some((ni,_deci,_w,src_rest)) = parse_number(src) {
                    return Some((Token::Data(Data::Val(Et::I32(ni))),src_rest));
    }   }   }   }

    // <1> 12345.0123
    if DIGITS.contains(c) {
        if let Some((ni,_deci,_w,src_rest)) = parse_number(src) {
            // println!("number parsed is {ni}+({_deci}/{_w}) = {}", ni as f32 + _deci as f32/_w as f32);
            return Some((Token::Data(Data::Val(Et::I32(ni))),src_rest));
        }
    // ; ,
    } if let (Some(&aux),src_next) = Aux::match_starts(src) {
        return Some((Token::Aux(aux.id),src_next));
    // <2> +-*/=;sum cnt
    } if let (Some(op),src_rest) = OPS.match_starts(src, None) {
    // } if let Some(op) = OPS.iter().find(|e|
    //     starts_with_and(src, e.name.as_char_slice(), not_char_and_digit).0
    // ) {
        // assert!(src.len()>=op.name.len());
        // let name_len = op.name.len();
        let (kind,len) = if let Some('&') = src_rest.first() {
            (Para::Ref,1)
        } else {
            (Para::Consumed,0)
        };
        return Some((Token::Op(op.clone(),kind),&src_rest[len..]));

    // <3> ( )
    } else if let Some(e) = Bracket::METAS.iter().find(|e|e.1==*c) {
        assert!(src.len()>=1);
        return Some((e.0.clone(),&src[1..]))

    // <3+1> { }
    } else if let Some(e) = Curly::METAS.iter().find(|e|e.1==*c) {
        assert!(src.len()>=1);
        // if let Token::Curly(Curly::RCurly) = e.0 {
        //     // <3+1+1> is jointly keyword } else
        //     let (src_next,_char_next) = skip_blank(&src[1..]);
        //     if let (true,src_next) = starts_with_and(src_next, Keyword::Else.name(), Some(is_blank_or_lcurly)) {
        //         return Some((Token::Kw(Keyword::Else),src_next));
        //     }
        // }
        return Some((e.0.clone(),&src[1..]))

    // <4|5|6|7> symbol | fndecl | fn | if then elif else end
    } else if is_sym_start(c) {
        if let Some((sym,src_rest)) = parse_symbol(src) {
            // <5> fn def
            if let ['f','n'] = sym {
                let Some((name,ps,src_rest)) = parse_fn_decl(src) else {
                    return None;
                };
                let name = name.iter().collect::<String>();
                let ps = ps.iter().map(|e: &&[char]|e.iter().collect::<String>()).collect();
                // let body = body.to_vec();
                // let fn_def = Fndef {name,ps,body};
                return Some((Token::Fndecl(name,ps),src_rest));
            }

            // <7> if then elif else end
            if let (Some(KeywordMeta{id,..}),_src_rest) = Keyword::all().match_starts(sym, None) {
                // assert_eq!(chars.len()+src_rest.len(),src.len());
                debug_assert!(_src_rest.is_empty());
                return Some((Token::Kw(id.clone()),src_rest));
            }

            let sym = sym.iter().collect::<String>();
            let fn_def = codes.get(&sym);

            // <4> symbol
            let Some(fn_def) = fn_def else {
                return Some((Token::Data(Data::Sym(sym)),src_rest));
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
            return Some((Token::Op(fn_opi, kind.0),&src_rest[kind.1..]));
        }
    }
    // Error, we canot diagonise
    None
}

#[derive(Clone, Copy,Debug)]
enum Ifflow { If,Then,Elif,Ifelse,Else,End }
impl Ifflow {
    // then elif else
    const INNER_PRINUM: PriNum = PriNum::P2; 
    // end
    const END_PRINUM: PriNum = PriNum::P1; 
}
// #[derive(Clone, Copy)]
// enum Iffflow { Iff,Then,Else }

#[derive(Clone, Copy,Debug)]
enum LeadBound {
    Head,
    Begin,
    End,
}
#[derive(Clone,Copy,Debug)]
enum Whileflow { While(usize,usize)/*stacksize,offset */,Body(Bound),Continue,Break(LeadBound),Else(LeadBound)/*,End*/}
impl Whileflow {
    const WHILE_BEGIN_PRINUM: PriNum = PriNum::P12;
    const BODY_BEGIN_PRINUM: PriNum = PriNum::P2;
    const BODY_END_PRINUM: PriNum = PriNum::P2;
    const BREAK_BEGIN_PRINUM: PriNum = PriNum::P3;
    const BREAK_END_PRINUM: PriNum = PriNum::P2;
    const WHILE_END_PRINUM: PriNum = PriNum::P1;
}

// struct SrcNext(bool);
fn ast_correspond(token:Token, whole:&[char], src:&[char], correspond:&mut CorrespondVec, codes:&mut FnCodeMap)->Option<CorreE> {
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
                    correspond.push(CorreE::Whc(Whileflow::Break(LeadBound::End)));
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
            correspond.push(CorreE::Ifc(Ifflow::If));
            // correspond.push_fndef(correspond.is_fndef());
            // correspond.push_condition(false);
            CorreE::Ifc(Ifflow::If) // we start a sub, use this
        }
        Token::Kw(Keyword::Then) => {
            start_new_exp = true;
            match correspond.last() {
                Some(CorreE::Ifc(Ifflow::If|Ifflow::Elif)) => {
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
                CorreE::IgnoreNextSteps
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
                    CorreE::IgnoreNextSteps
                }
                Some(CorreE::Ifc(Ifflow::If|Ifflow::Elif)) => {
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
                    correspond.pop_fndef();
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
                    CorreE::IgnoreNextSteps
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
                Some(CorreE::Whc(Whileflow::Body(Bound::Begin))) => {
                    correspond.update(CorreE::Whc(Whileflow::Break(LeadBound::Begin)));
                    CorreE::Whc(Whileflow::Break(LeadBound::Begin))
                }
                Some(CorreE::Ifc(Ifflow::Then|Ifflow::Ifelse|Ifflow::Else)) => {
                    correspond.update(CorreE::Whc(Whileflow::Break(LeadBound::Begin)));
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
enum Indication {
    Data(Data),
    Op(Opi,Para),
    Sub(Bound),
    Pr(Bracket),
}


// enum AndTodoNext {
//     TrueDo, FalseDo,
// }
#[derive(Debug)]
enum PopSubjectMatter<'a> {
    Op(Opi,Para),
    Pr(PriNum,RetRule),
    PrCond(PriNum,RetRule,fn(bool,&mut FlowBool),&'a mut FlowBool),
    PrAgain(PriNum,RetRule,usize,usize), // offset
    // ConditionCalc(PriNum),
    // BreakCalc(PriNum),
    Donot,
}
fn do_if_then(cond:bool, flowbool:& mut FlowBool) {
    debug_assert!(matches!(flowbool,FlowBool::If(IfState::If0)));
    if cond {
        *flowbool = FlowBool::If(IfState::ThenDo);
    } else {
        *flowbool = FlowBool::If(IfState::ThenDonot);
    }
}
fn do_if_else(cond:bool, flowbool:& mut FlowBool) {
    debug_assert!(matches!(flowbool,FlowBool::If(IfState::If0)));
    if !cond {
        *flowbool = FlowBool::If(IfState::ElseDo);
    } else {
        *flowbool = FlowBool::If(IfState::ElseDonot);
    }
}

fn do_if_ast_null(_cond:bool, _flowbool:& mut FlowBool) {
}
fn do_while_body<'a>(cond:bool, flowbool:&'a mut FlowBool) {
    let FlowBool::While(whilestate@WhileState::While1,..) = flowbool else {
        panic!("the grammmer error");
    };
    if cond {
        *whilestate = WhileState::BodyDo;
    } else {
        *whilestate = WhileState::BodyDonot;
    }
}

fn push_exp<'a>(corre:CorreE, corre_size: usize,frame_stack: &mut FrameVec, cond_stack: &'a mut CondStack)->PopSubjectMatter<'a> {
    match cond_stack.last() {
        Some(FlowBool::If(ifstate)) => {
            match ifstate {
                IfState::If0|IfState::ThenDo|IfState::ElseDo
                    => {}
                IfState::ThenDone => {
                    if let CorreE::Ifc(Ifflow::End) = corre {
                        cond_stack.pop();
                    }
                    return PopSubjectMatter::Donot;
                }
                IfState::ThenDonot => {
                    match corre {
                        CorreE::Ifc(Ifflow::End) => {
                            cond_stack.pop();
                        }
                        CorreE::Ifc(Ifflow::Else) => {
                            cond_stack.update_if(IfState::ElseDo);
                        }
                        CorreE::Ifc(Ifflow::Elif) => {
                            cond_stack.update_if(IfState::If0);
                        }
                        _=>{}
                    }
                    return PopSubjectMatter::Donot;
                }
                IfState::ElseDonot => {
                    if let CorreE::Ifc(Ifflow::End) = corre {
                        cond_stack.pop();
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
                                CorreE::Whc(Whileflow::Else(LeadBound::Begin)) =>
                                    cond_stack.update_while(WhileState::ElseDo),
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

    match corre {
        CorreE::Fnast(_) => unreachable!("should be done in ast part"),
        CorreE::Ifc(Ifflow::If) => {
            //1
            let _ = push_frame(frame_stack);
            cond_stack.push(FlowBool::If(IfState::If0));
            PopSubjectMatter::Donot
        }
        CorreE::Ifc(Ifflow::Then) => {
            //1
            debug_assert!(matches!(cond_stack.last(),Some(FlowBool::If(IfState::If0))));
            let Some(flowbool) = cond_stack.last_mut() else {
                unreachable!("internal error");
            };
            PopSubjectMatter::PrCond(Ifflow::INNER_PRINUM,RetRule::Ignore,do_if_then,flowbool)
        }
        CorreE::Ifc(Ifflow::Ifelse) => {
            debug_assert!(matches!(cond_stack.last(),Some(FlowBool::If(IfState::If0))));
            let Some(flowbool) = cond_stack.last_mut() else {
                unreachable!("internal error");
            };
            PopSubjectMatter::PrCond(Ifflow::INNER_PRINUM,RetRule::Ignore,do_if_else,flowbool)
        }
        CorreE::Ifc(Ifflow::Else) => {
            //1
            debug_assert!(matches!(cond_stack.last_mut(),Some(FlowBool::If(IfState::ThenDo))));
            cond_stack.update_if(IfState::ThenDone);
            PopSubjectMatter::Pr(Ifflow::INNER_PRINUM,RetRule::Ignore)
        }
        CorreE::Ifc(Ifflow::Elif) => {
            //1
            debug_assert!(matches!(cond_stack.last_mut(),Some(FlowBool::If(IfState::ThenDo))));
            cond_stack.update_if(IfState::ThenDone);
            PopSubjectMatter::Pr(Ifflow::INNER_PRINUM,RetRule::Ignore)
        }
        CorreE::Ifc(Ifflow::End) => {
            //1
            debug_assert!(matches!(cond_stack.last_mut(),Some(FlowBool::If(IfState::ThenDo|IfState::ElseDo))));
            cond_stack.update_if(IfState::ThenDone);
            // cond_stack.update_if(IfState::ElseDone);
            cond_stack.pop(); // the cond of if is done
            PopSubjectMatter::Pr(Ifflow::END_PRINUM, RetRule::Ignore)
        }

        // while running structure
        CorreE::Whc(Whileflow::While(stacksize,offset)) => {
            let _ = push_frame(frame_stack);
            cond_stack.push(FlowBool::While(WhileState::While1,stacksize,offset));
            PopSubjectMatter::Pr(Whileflow::WHILE_BEGIN_PRINUM, RetRule::Ignore)
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
                    PopSubjectMatter::PrAgain(Whileflow::BODY_END_PRINUM,RetRule::Ignore,*stacksize,*offset)
                }
                FlowBool::If(IfState::ThenDo|IfState::ElseDo) => {
                    while let Some(FlowBool::If(ifstate)) = cond_stack.last() {
                        debug_assert!(matches!(ifstate,IfState::ThenDo|IfState::ElseDo));
                        cond_stack.pop();
                    }
                    let Some(FlowBool::While(WhileState::BodyDo,stacksize,offset)) = cond_stack.last() else {
                        unreachable!("never reach here");
                    };
                    PopSubjectMatter::PrAgain(Whileflow::BODY_END_PRINUM,RetRule::Ignore,*stacksize,*offset)
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
                FlowBool::If(IfState::ThenDo|IfState::ElseDo) => {
                    while let Some(FlowBool::If(ifstate)) = cond_stack.last() {
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
            unreachable!("should be done in ast procedure");
            // PopSubjectMatter::Donot
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
enum AndTodo {
    Try,
    None,
    ConditionBack(bool),
    BreakBack, // donot need the break value, just store in the frame, get the value at the while-end
}
fn src_again<'a>(whole:&'a[char], stacksize:usize,offset:usize,correspond:&mut CorrespondVec)->&'a[char] {
    match correspond.len().cmp(&stacksize) {
        std::cmp::Ordering::Less =>
            correspond.push(CorreE::Whc(Whileflow::While(stacksize,offset))),
        std::cmp::Ordering::Equal =>
            correspond.update(CorreE::Whc(Whileflow::While(stacksize,offset))),
        std::cmp::Ordering::Greater =>
            unreachable!("internal error"),
    }
    debug_assert_eq!(stacksize,correspond.len());
    &whole[offset..]
}
fn decide_todo(subject_matter:PopSubjectMatter,codes:&FnCodeMap,symbols:&mut SymbolMap, frame: &mut Frame)->Option<()> {
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
            let cause = (prinum,RetRule::Ignore);
            try_pop_exp_util(codes,symbols,frame,cause);
            clear_data(frame);
            if let PriNum::P0|PriNum::P1 = prinum {Some(())} else {None}
        }
        PopSubjectMatter::Donot => None, // do nothing
    }
}

fn pop_frame_or_exit(frame_stack: &mut FrameVec,symbols:&SymbolMap)->Option<Option<Et>> {
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

// if I clear all but keep the last, added here

fn push_data(v:Data, stack: &mut Vec<Data>) {
    println!("\t++++ push data {v:?}");
    stack.push(v);
}
fn push_action(opi:(Opi,Para), stack: &mut Vec<(Opi,Para)>) {
    println!("\t++++ push op {:?} {:?}",opi.0.name,opi.1);
    stack.push(opi);
}
fn push_fndef(fndef:Fndef, codes:&mut FnCodeMap) {
    println!("\t++++ push fn {:?}", fndef);
    codes.insert(fndef.name.clone(), fndef);
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
    const fn exp_start(&self)->bool {
        self.exp_start
    }
    fn set_exp_start(&mut self) {
        self.exp_start = true;
    }
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
/* fn n x y = x+y, */
#[derive(Clone,Debug)]
struct Fndef {
    name: String,
    ps: Vec<String>,
    body: Vec<char>,
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
/// while state machine
/// which control the flow of while loop flow run as its design
/// this value is not belonged to user-code just inner state
/// includes all kinds of flags such while body continue break else etc..
#[derive(Debug)]
enum WhileState {
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
enum IfState {
    If0,
    ThenDo,ThenDone,ThenDonot,
    ElseDo,/*ElseDone,*/ElseDonot,
    /*End,*/
}
#[derive(Debug)]
enum FlowBool {
    // while-state, stack-size, offset
    While(WhileState,usize,usize),
    If(IfState),
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

#[derive(Clone, Copy,Debug)]
enum Bound {
    Begin,End,
}
#[derive(Clone,Debug)]
enum Fnast {
    Decl(String,Vec<String>,usize),
    End,
}

// #[derive(Clone, Copy)]
// enum Verify {
//     Literal,
//     Literaling(usize),
// }
#[derive(Clone,Debug)]
enum CorreE {
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
struct Context {
    frame_stack: FrameVec,
    cond_stack: CondStack,
    symbols: SymbolMap,
    correspond: CorrespondVec,
    fn_codes: FnCodeMap,
}


