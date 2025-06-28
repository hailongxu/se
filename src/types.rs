use crate::token::{MatchStart, ToChars};


#[derive(Clone, Copy,Debug,Eq,PartialEq, Ord,PartialOrd)]
pub enum Et {
    // Bool(bool),
    I32(i32),
    // Real(f32)
}

impl Et {
    pub(crate) fn as_i32(&self)->&i32 {
        let Et::I32(v) = self else {
            panic!("the type is not supported");
        };
        v
    }
}

#[derive(Clone,Debug)]
pub(crate) enum Data {
    Val(Et),
    Sym(String)
}

#[derive(Debug,Clone,Copy,PartialEq, PartialOrd)]
pub(crate) enum PriNum {
    // P0: exit; P1: pop frame; P2: minimum action num
    P0, P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, P11, P12
}


type Sstr = &'static str;
type Schars = &'static[char];
#[derive(Clone, Copy,Debug)]
pub(crate) enum Keyword
{
    If,Then,Elif,Else,Fn,End,While,Continue,Break,
}
pub(crate) struct KeywordMeta {
    pub(crate) id: Keyword,
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
    pub(crate) const fn name(&self)->Schars {
        let i = *self as usize;
        Self::METAS[i].name
    }
    pub(crate) const fn all()->&'static[KeywordMeta] {
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

// end of progamm
#[derive(Debug,Clone, Copy)]
pub(crate) struct Exit;
impl Exit {
    pub(crate) const PRINUM:PriNum = PriNum::P0;
}


#[derive(Debug,Clone, Copy)]
pub(crate) enum RetRule {
    None,
    Ignore,
}