use se::parse;
use se::Et;


#[test]
pub fn test_if_while() {
    let ss = [
        ("i=1; while i<4 {i=i+1 break 4+i,}",6),
        ("i=1; while i<2 {i=i+1; if 1 then continue end break 4,} else {break i+10,}",12)
    ];

    test_exps(ss);
}

#[test]
pub fn test_if() {
    let ss = [
        ("if 0  else 8 end",8),
        ("if if 1 then 0 elif 0 then 30 else 0 end  then 2 elif 3 then 4 else 5 end",4)
    ];

    test_exps(ss);
}

#[test]
pub fn test_avg() {
    let ss = [
    (r"
    100
    32
    avg
    ", 66),
    (r"
    16
    avg
    ", 16)
    ];
    test_exps(ss);
}

#[test]
pub fn test_fn() {
    let ss = [
        ("fn f x=x*(2+3)*x , f 1", 5),
        ("fn f2 x = x*7, 2 f2& + 3 sum 4", 2+14+3+4)
    ];
    test_exps(ss);
}

#[test]
pub fn test_math_exp() {

    let ss = [
        ("-5 * ( ( -3 + 6 ) )", -5*((-3+6))),
        ("31 cnt& cnt",2),
        ("57/12",57/12),
        ("1900 2*", 1900*2),
        ("sum 2 3 4", 2+3+4),
        ("3+5*2", 3+5*2),
    ];

    test_exps(ss);
}

#[test]
fn test_none() {
    let s = "\r";
    test_exp_none(s);
}

fn test_exps<const N:usize>(ss:[(&str,i32);N]) {
    for (s,r) in ss {
        test_exp(s,r);
    }
}

fn test_exp(s:&str, ret:i32) {
    let ss = s;
    let s = s.chars().collect::<Box<[char]>>();
    let s = s.as_ref();
    // let Some(vv) = parse_symbol(s) else {return};
    // let vv = skip_blank_back(s);
    // let vv = parse_fn(s);
    let vv = parse(s);
    println!("{ss}==={vv:?}");
    assert_eq!(vv, Some(Et::I32(ret)));
}

fn test_exp_none(s:&str) {
    let ss = s;
    let s = s.chars().collect::<Box<[char]>>();
    let s = s.as_ref();
    let vv = parse(s);
    println!("{ss:?}==={vv:?}");
    assert_eq!(vv, None);
}