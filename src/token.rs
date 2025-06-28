
use crate::FnCodeMap;
use crate::types::{Exit,Et,Data,Keyword,KeywordMeta,PriNum};
use crate::ast::{Sym,Aux};
use crate::pop::{Opi,Para,OPS};

macro_rules! DIGITS { () => {'0'..='9'}; }
macro_rules! LOWER_CHARS { () => {'a'..='z'}; }
macro_rules! UPPER_CHARS { () => {'A'..='Z'}; }


pub(crate) fn token_next<'a>(src:&'a[char], sign_number:bool, codes:&FnCodeMap)->Option<(Token,&'a[char])> {
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
            // let fn_name = Sym::String(sym);
            // let fn_dw = DataWhere::Any(fn_def.ps.len() as i32);
            // const FN_PRINUM: PriNum = PriNum::P10;
            // const FN_DO: Act = Act::Fn(op_fn_do);
            // const FN_RET: Ret = Ret::Value;
            // let fn_opi = Opi::new(fn_name, FN_DO, FN_PRINUM, fn_dw, FN_RET);
            let fn_opi = Opi::from_fn(sym, fn_def.ps.len());
            return Some((Token::Op(fn_opi, kind.0),&src_rest[kind.1..]));
        }
    }
    // Error, we canot diagonise
    None
}



// 后面考虑加入啥（数据是引用，这样能减轻数据的传递）
#[derive(Debug,Clone)]
pub(crate) enum Token {
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


fn skip_blank_back(src:&[char])->(&[char],Option<char>) {
    let Some(p) = src.iter().rev().position(|e|!SKIP_CHARS.contains(e)) else {
        // 没有非空格
        return (&[],None);
    };
    assert!(p>=0);
    (&src[..src.len()-p],Some(src[src.len()-p-1]))
}

pub(crate) fn skip_blank(src:&[char])->(&[char],Option<char>) {
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

fn skip_space_back(src:&[char])->(&[char],Option<char>) {
    let Some(p) = src.iter().rev().position(|e|*e!=' ') else {
        // 没有非空格
        return (&[],None);
    };
    assert!(p>=0);
    (&src[..src.len()-p],Some(src[src.len()-p-1]))
}



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

const fn is_sym_start(c:&char)->bool {
    match c {
        UPPER_CHARS!() => true,
        LOWER_CHARS!() => true,
        _ => false,
    }
    // UPPER_CHARS.contains(&c) || LOWER_CHARS.contains(&c)
}


pub(crate) trait ToChars {
    fn to_chars(&self)->&[char];
}

pub(crate) trait MatchStart<Item:ToChars> {
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

pub(crate) fn test_next_token_else(src:&[char])->(bool,&[char]) {
    let (src_next,_char_next) = skip_blank(src);
    // the next char cond equaliverlent to parse_symbol
    starts_with_and(src_next, Keyword::Else.name(), Some(not_char_and_digit))
}

pub(crate) fn parse_symbol(src:&[char])->Option<(&[char],&[char])> {
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

#[derive(Clone,Copy,Debug)]
pub(crate) enum Bracket {
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
    pub(crate) const fn prinum(&self)->PriNum {
        self.info().2
    }
}

#[derive(Clone,Copy,Debug)]
pub(crate) enum Curly {
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

/* fn n x y = x+y, */
#[derive(Clone,Debug)]
pub(crate) struct Fndef {
    pub(crate) name: String,
    pub(crate) ps: Vec<String>,
    pub(crate) body: Vec<char>,
}


#[test]
fn test_parse_number() {
    fn test_some(s:&str,ret: (i32,i32,i32,&[char])) {
        let input = s;
        let s = s.chars().collect::<Box<[char]>>();
        let s = s.as_ref();
        let r = parse_number(s);
        let r = r.unwrap();
        println!("{input}  <==>  {r:?}");
        assert_eq!(r,ret);
    }
    let s = "1万3百20";
    test_some(s,(10320,0,1,&[]));
    let s = "1万3百20.8";
    test_some(s,(10320,8,10,&[]));
    let s = "1万3百20.08";
    test_some(s,(10320,8,100,&[]));
}

#[test]
fn test_parse_symbol() {
    let s = "ss";
    let str = s;
    let s = s.chars().collect::<Box<[char]>>();
    let s = s.as_ref();

    let r = parse_symbol(s);
    println!("{str} <=> {r:?}");
    assert_eq!(r,Some((['s','s'].as_slice(),[].as_slice())));
}