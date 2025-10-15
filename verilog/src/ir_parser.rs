use indexmap::IndexMap;
use z3::{ast::{Ast, Bool, Dynamic, Int, BV}, Context};

type InlineKey = (String, Vec<u64>);
type InlineMemo = IndexMap<InlineKey, Expr>;

// === Bring your IR into scope (adjust paths) ===
use ir::{SMVEnv, VarType, ReturnType, Variable};

// ---------------------------
// S-expression + Mini-IR
// ---------------------------

#[derive(Clone, Debug)]
enum SExp { Atom(String), List(Vec<SExp>) }

#[derive(Clone, Debug)]
enum Sort { Bool, Int, BV(u32) }

#[derive(Clone, Debug)]
enum Expr {
    Sym(String),
    BoolConst(bool),
    IntConst(i64),
    BVConst { bits: String },
    Eq(Box<Expr>, Box<Expr>),
    Ite(Box<Expr>, Box<Expr>, Box<Expr>),
    Extract { hi: u32, lo: u32, e: Box<Expr> },
    And(Vec<Expr>),
    Or(Vec<Expr>),
    Not(Box<Expr>),
    Xor(Vec<Expr>),     
    BVXor(Vec<Expr>),   
    App(String, Vec<Expr>),
}

#[derive(Clone, Debug)]
struct FnDef {
    params: Vec<(String, Sort)>,
    ret: Sort,
    body: Expr,
}

// ---------------------------
// Tokenize / Parse SExp
// ---------------------------

fn strip_pipes(s: &str) -> String {
    let s = s.trim();
    if s.starts_with('|') && s.ends_with('|') && s.len() >= 2 { s[1..s.len()-1].to_string() }
    else { s.to_string() }
}

fn tokenize(source: &str) -> Vec<String> {
    // strip ; comments
    let mut cleaned = String::with_capacity(source.len());
    for line in source.lines() {
        if let Some(i) = line.find(';') { cleaned.push_str(&line[..i]); cleaned.push('\n'); }
        else { cleaned.push_str(line); cleaned.push('\n'); }
    }
    let s = cleaned;

    let mut toks = Vec::new();
    let ch: Vec<char> = s.chars().collect();
    let mut i = 0;
    while i < ch.len() {
        match ch[i] {
            c if c.is_whitespace() => i += 1,
            '(' | ')' => { toks.push(ch[i].to_string()); i += 1; }
            '|' => {
                let start = i; i += 1;
                while i < ch.len() && ch[i] != '|' { i += 1; }
                if i < ch.len() { i += 1; }
                toks.push(ch[start..i].iter().collect());
            }
            _ => {
                let start = i;
                while i < ch.len() && !ch[i].is_whitespace() && ch[i] != '(' && ch[i] != ')' { i += 1; }
                toks.push(ch[start..i].iter().collect());
            }
        }
    }
    toks
}

fn parse_list(tokens: &[String], pos: &mut usize) -> Result<SExp, String> {
    let mut out = Vec::new();
    while *pos < tokens.len() {
        match tokens[*pos].as_str() {
            "(" => { *pos += 1; out.push(parse_list(tokens, pos)?); }
            ")" => { *pos += 1; return Ok(SExp::List(out)); }
            tok => { out.push(SExp::Atom(tok.to_string())); *pos += 1; }
        }
    }
    Err("Unbalanced parentheses".into())
}

fn parse_sexps(s: &str) -> Result<Vec<SExp>, String> {
    let toks = tokenize(s);
    let mut pos = 0;
    let mut items = Vec::new();
    while pos < toks.len() {
        match toks[pos].as_str() {
            "(" => { pos += 1; items.push(parse_list(&toks, &mut pos)?); }
            ")" => return Err("Unexpected ')'".into()),
            _   => { items.push(SExp::Atom(toks[pos].clone())); pos += 1; }
        }
    }
    Ok(items)
}

// ---------------------------
// SMT sorts / Expr parser
// ---------------------------

fn parse_sort(s: &SExp) -> Result<Sort, String> {
    match s {
        SExp::Atom(a) if a == "Bool" => Ok(Sort::Bool),
        SExp::Atom(a) if a == "Int"  => Ok(Sort::Int),
        SExp::List(v) if v.len() == 3 => {
            if let (SExp::Atom(u), SExp::Atom(bv), SExp::Atom(n)) = (&v[0], &v[1], &v[2]) {
                if u == "_" && bv == "BitVec" {
                    let w: u32 = n.parse().map_err(|_| "Bad BitVec width".to_string())?;
                    return Ok(Sort::BV(w));
                }
            }
            Err(format!("Unsupported sort: {:?}", s))
        }
        _ => Err(format!("Unsupported sort: {:?}", s)),
    }
}

fn parse_expr(e: &SExp) -> Result<Expr, String> {
    match e {
        SExp::Atom(a) => {
            if a == "true"  { return Ok(Expr::BoolConst(true)); }
            if a == "false" { return Ok(Expr::BoolConst(false)); }
            if a.starts_with("#b") { return Ok(Expr::BVConst { bits: a[2..].to_string() }); }
            if let Ok(i) = a.parse::<i64>() { return Ok(Expr::IntConst(i)); }
            return Ok(Expr::Sym(strip_pipes(a)));
        }
        SExp::List(v) if v.is_empty() => Err("Empty list".into()),
        SExp::List(v) => {
            // ((_ extract hi lo) e)
            if let SExp::List(head) = &v[0] {
                if head.len() == 4 {
                    if let (SExp::Atom(u), SExp::Atom(ex), SExp::Atom(hi), SExp::Atom(lo)) =
                        (&head[0], &head[1], &head[2], &head[3]) {
                        if u == "_" && ex == "extract" && v.len() == 2 {
                            let hi: u32 = hi.parse().map_err(|_| "bad extract hi".to_string())?;
                            let lo: u32 = lo.parse().map_err(|_| "bad extract lo".to_string())?;
                            return Ok(Expr::Extract { hi, lo, e: Box::new(parse_expr(&v[1])?) });
                        }
                    }
                }
            }

            // head is an atom (operator / symbol)
            let head = match &v[0] { SExp::Atom(a) => a.as_str(), _ => return Err("Bad head".into()) };
            match head {
                "=" => {
                    if v.len() != 3 { return Err("= expects 2 args".into()); }
                    Ok(Expr::Eq(Box::new(parse_expr(&v[1])?), Box::new(parse_expr(&v[2])?)))
                }
                "ite" => {
                    if v.len() != 4 { return Err("ite expects 3 args".into()); }
                    Ok(Expr::Ite(
                        Box::new(parse_expr(&v[1])?),
                        Box::new(parse_expr(&v[2])?),
                        Box::new(parse_expr(&v[3])?)
                    ))
                }
                "and" => {
                    let mut xs = Vec::new();
                    for a in &v[1..] { xs.push(parse_expr(a)?); }
                    Ok(Expr::And(xs))
                }
                "or" => {
                    let mut xs = Vec::new();
                    for a in &v[1..] { xs.push(parse_expr(a)?); }
                    Ok(Expr::Or(xs))
                }
                "not" => {
                    if v.len() != 2 { return Err("not expects 1 arg".into()); }
                    Ok(Expr::Not(Box::new(parse_expr(&v[1])?)))
                }
                "xor" => {
                    // Boolean XOR: accept 1+ args (xor a) == a; (xor a b c) == a ^ b ^ c
                    let mut xs = Vec::with_capacity(v.len().saturating_sub(1));
                    for a in &v[1..] { xs.push(parse_expr(a)?); }
                    Ok(Expr::Xor(xs))
                }
                "bvxor" => {
                    // Bitvector XOR: 2+ args
                    let mut xs = Vec::with_capacity(v.len().saturating_sub(1));
                    for a in &v[1..] { xs.push(parse_expr(a)?); }
                    Ok(Expr::BVXor(xs))
                }
                // Otherwise: helper application
                _ => {
                    let name = strip_pipes(&v[0].as_atom().unwrap_or_default());
                    let mut args = Vec::new();
                    for a in &v[1..] { args.push(parse_expr(a)?); }
                    Ok(Expr::App(name, args))
                }
            }
        }
    }
}

trait AsAtom {
    fn as_atom(&self) -> Option<String>;
}
impl AsAtom for SExp {
    fn as_atom(&self) -> Option<String> {
        if let SExp::Atom(a) = self { Some(a.clone()) } else { None }
    }
}

// ---------------------------
// Helpers: inline-on-demand
// ---------------------------

type FnTable = IndexMap<String, FnDef>;

fn subst_expr(e: &Expr, sub: &IndexMap<String, Expr>) -> Expr {
    match e {
        Expr::Sym(s) => sub.get(s).cloned().unwrap_or_else(|| Expr::Sym(s.clone())),
        Expr::BoolConst(_) | Expr::IntConst(_) | Expr::BVConst{..} => e.clone(),
        Expr::Eq(a,b) => Expr::Eq(Box::new(subst_expr(a, sub)), Box::new(subst_expr(b, sub))),
        Expr::Ite(c,t,ee) => Expr::Ite(
            Box::new(subst_expr(c, sub)),
            Box::new(subst_expr(t, sub)),
            Box::new(subst_expr(ee, sub))
        ),
        Expr::Extract{hi,lo,e:ee} => Expr::Extract{ hi:*hi, lo:*lo, e:Box::new(subst_expr(ee, sub)) },
        Expr::And(xs)   => Expr::And(xs.iter().map(|x| subst_expr(x, sub)).collect()),
        Expr::Or(xs)    => Expr::Or(xs.iter().map(|x| subst_expr(x, sub)).collect()),
        Expr::Not(x)    => Expr::Not(Box::new(subst_expr(x, sub))),
        Expr::Xor(xs)   => Expr::Xor(xs.iter().map(|x| subst_expr(x, sub)).collect()),
        Expr::BVXor(xs) => Expr::BVXor(xs.iter().map(|x| subst_expr(x, sub)).collect()),
        Expr::App(n, args) => Expr::App(n.clone(), args.iter().map(|x| subst_expr(x, sub)).collect()),
    }
}


fn inline_helpers(e: &Expr, fns: &FnTable, depth: usize) -> Result<Expr, String> {
    if depth > 256 { return Err("helper expansion depth exceeded".into()); }
    match e {
        Expr::App(name, args) if fns.contains_key(name) => {
            let def = &fns[name];
            if def.params.len() != args.len() {
                return Err(format!("arity mismatch in call {}: expected {}, got {}", name, def.params.len(), args.len()));
            }
            // first inline args
            let mut inlined_args = Vec::new();
            for a in args { inlined_args.push(inline_helpers(a, fns, depth+1)?); }
            // build substitution map
            let mut sub = IndexMap::new();
            for ((p, _psort), act) in def.params.iter().zip(inlined_args.into_iter()) {
                sub.insert(p.clone(), act);
            }
            // substitute into body, then continue inlining recursively
            let body_sub = subst_expr(&def.body, &sub);
            inline_helpers(&body_sub, fns, depth+1)
        }
        // Recurse
        Expr::Eq(a,b) => Ok(Expr::Eq(Box::new(inline_helpers(a,fns,depth+1)?), Box::new(inline_helpers(b,fns,depth+1)?))),
        Expr::Ite(c,t,ee) => Ok(Expr::Ite(
            Box::new(inline_helpers(c,fns,depth+1)?),
            Box::new(inline_helpers(t,fns,depth+1)?),
            Box::new(inline_helpers(ee,fns,depth+1)?),
        )),
        Expr::Extract{hi,lo,e:ee} => Ok(Expr::Extract{hi:*hi,lo:*lo,e:Box::new(inline_helpers(ee,fns,depth+1)?) }),
        Expr::And(xs) => Ok(Expr::And(xs.iter().map(|x| inline_helpers(x,fns,depth+1)).collect::<Result<Vec<_>,_>>()?)),
        Expr::Or(xs)  => Ok(Expr::Or(xs.iter().map(|x| inline_helpers(x,fns,depth+1)).collect::<Result<Vec<_>,_>>()?)),
        Expr::Not(x)  => Ok(Expr::Not(Box::new(inline_helpers(x,fns,depth+1)?))),
        // leaves
        _ => Ok(e.clone()),
    }
}

// ---------------------------
// Expr -> Z3 AST
// ---------------------------

struct TyCtxt { vars: IndexMap<String, Sort> }

fn bv_from_bits<'ctx>(ctx: &'ctx Context, bits: &str) -> BV<'ctx> {
    let width = bits.len() as u32;
    let mut v: i64 = 0;
    for c in bits.chars() { v = (v << 1) | if c == '1' { 1 } else { 0 }; }
    BV::from_i64(ctx, v, width)
}

fn expr_to_ast<'ctx>(
    e: &Expr,
    ctx: &'ctx Context,
    st: &IndexMap<&'ctx str, Dynamic<'ctx>>,
) -> Result<Dynamic<'ctx>, String> {
    match e {
        Expr::Sym(s) => {
            let key: &'static str = Box::leak(s.clone().into_boxed_str());
            st.get(key).cloned().ok_or_else(|| format!("Unknown symbol: {}", s))
        }
        Expr::BoolConst(b) => Ok(Bool::from_bool(ctx, *b).into()),
        Expr::IntConst(i)  => Ok(Int::from_i64(ctx, *i).into()),
        Expr::BVConst{bits} => Ok(bv_from_bits(ctx, bits).into()),

        Expr::Eq(a,b) => {
            let da = expr_to_ast(a,ctx,st)?; let db = expr_to_ast(b,ctx,st)?;
            if let (Some(x), Some(y)) = (da.as_bool(), db.as_bool()) { Ok(x._eq(&y).into()) }
            else if let (Some(x), Some(y)) = (da.as_int(), db.as_int()) { Ok(x._eq(&y).into()) }
            else if let (Some(x), Some(y)) = (da.as_bv(), db.as_bv())   { Ok(x._eq(&y).into()) }
            else { Err("Type mismatch in '='".into()) }
        }
        Expr::Ite(c, t, e2) => {
            let bc = expr_to_ast(c, ctx, st)?.as_bool().ok_or("ITE cond not Bool")?;
            let dt = expr_to_ast(t, ctx, st)?;
            let de = expr_to_ast(e2, ctx, st)?;
            if let (Some(tt), Some(ee)) = (dt.as_bool(), de.as_bool()) {
                Ok(Bool::ite(&bc, &tt, &ee).into())
            } else if let (Some(tt), Some(ee)) = (dt.as_int(), de.as_int()) {
                Ok(Bool::ite(&bc, &tt, &ee).into())
            } else if let (Some(tt), Some(ee)) = (dt.as_bv(), de.as_bv()) {
                Ok(Bool::ite(&bc, &tt, &ee).into())
            } else {
                Err("ITE branches have different types".into())
            }
        }
        Expr::Extract{hi,lo,e} => {
            let bv = expr_to_ast(e,ctx,st)?.as_bv().ok_or("extract on non-BV")?;
            Ok(bv.extract(*hi,*lo).into())
        }
        Expr::And(xs) => {
            let mut bs: Vec<Bool> = Vec::new();
            for x in xs { bs.push(expr_to_ast(x,ctx,st)?.as_bool().ok_or("and arg not Bool")?); }
            let refs: Vec<&Bool> = bs.iter().collect();
            Ok(Bool::and(ctx, &refs).into())
        }
        Expr::Or(xs) => {
            let mut bs: Vec<Bool> = Vec::new();
            for x in xs { bs.push(expr_to_ast(x,ctx,st)?.as_bool().ok_or("or arg not Bool")?); }
            let refs: Vec<&Bool> = bs.iter().collect();
            Ok(Bool::or(ctx, &refs).into())
        }
        Expr::Xor(xs) => {
            // boolean xor via left fold using != (i.e., not equal)
            if xs.is_empty() {
                return Err("xor expects at least 1 argument".into());
            }
            let mut bs: Vec<Bool> = Vec::with_capacity(xs.len());
            for x in xs {
                let b = expr_to_ast(x, ctx, st)?.as_bool().ok_or("xor arg not Bool")?;
                bs.push(b);
            }
            // (xor a) == a; (xor a b c) == ((a != b) != c) ...
            let mut acc = bs[0].clone();
            for b in bs.iter().skip(1) {
                acc = acc._eq(b).not();
            }
            Ok(acc.into())
        }
        Expr::BVXor(xs) => {
            if xs.len() < 2 {
                return Err("bvxor expects at least 2 arguments".into());
            }
            let mut it = xs.iter();
            let first = expr_to_ast(it.next().unwrap(), ctx, st)?.as_bv().ok_or("bvxor arg not BV")?;
            let mut acc = first;
            for x in it {
                let bv = expr_to_ast(x, ctx, st)?.as_bv().ok_or("bvxor arg not BV")?;
                acc = acc.bvxor(&bv);
            }
            Ok(acc.into())
        }        
        Expr::Not(x) => Ok(expr_to_ast(x,ctx,st)?.as_bool().ok_or("not arg not Bool")?.not().into()),
        Expr::App(name, args) => {
            // helpers to parse BV args
            let mut as_bv_list = |min_arity: usize, opname: &str| -> Result<Vec<BV<'ctx>>, String> {
                if args.len() < min_arity {
                    return Err(format!("{} expects at least {} arg(s)", opname, min_arity));
                }
                let mut out = Vec::with_capacity(args.len());
                for a in args {
                    let d = expr_to_ast(a, ctx, st)?;
                    out.push(d.as_bv().ok_or_else(|| format!("{} arg not BV", opname))?);
                }
                Ok(out)
            };
            let mut as_bv_pair = |opname: &str| -> Result<(BV<'ctx>, BV<'ctx>), String> {
                if args.len() != 2 {
                    return Err(format!("{} expects 2 arguments", opname));
                }
                let a0 = expr_to_ast(&args[0], ctx, st)?.as_bv().ok_or_else(|| format!("{} arg0 not BV", opname))?;
                let a1 = expr_to_ast(&args[1], ctx, st)?.as_bv().ok_or_else(|| format!("{} arg1 not BV", opname))?;
                Ok((a0, a1))
            };
            let mut as_bv_unary = |opname: &str| -> Result<BV<'ctx>, String> {
                if args.len() != 1 {
                    return Err(format!("{} expects 1 argument", opname));
                }
                let a0 = expr_to_ast(&args[0], ctx, st)?.as_bv().ok_or_else(|| format!("{} arg not BV", opname))?;
                Ok(a0)
            };

            match name.as_str() {
                // N-ary bitwise
                "bvand" => {
                    let mut xs = as_bv_list(2, "bvand")?;
                    let mut acc = xs.remove(0);
                    for x in xs { acc = acc.bvand(&x); }
                    Ok(acc.into())
                }
                "bvor" => {
                    let mut xs = as_bv_list(2, "bvor")?;
                    let mut acc = xs.remove(0);
                    for x in xs { acc = acc.bvor(&x); }
                    Ok(acc.into())
                }
                "bvxor" => {
                    let mut xs = as_bv_list(2, "bvxor")?;
                    let mut acc = xs.remove(0);
                    for x in xs { acc = acc.bvxor(&x); }
                    Ok(acc.into())
                }
                "bvnand" => {
                    let mut xs = as_bv_list(2, "bvnand")?;
                    let mut acc = xs.remove(0);
                    for x in xs { acc = acc.bvand(&x); }
                    Ok(acc.bvnot().into())
                }
                "bvnor" => {
                    let mut xs = as_bv_list(2, "bvnor")?;
                    let mut acc = xs.remove(0);
                    for x in xs { acc = acc.bvor(&x); }
                    Ok(acc.bvnot().into())
                }
                "bvxnor" => {
                    let mut xs = as_bv_list(2, "bvxnor")?;
                    let mut acc = xs.remove(0);
                    for x in xs { acc = acc.bvxor(&x); }
                    Ok(acc.bvnot().into())
                }

                // Unary bitwise/arithmetic
                "bvnot" => Ok(as_bv_unary("bvnot")?.bvnot().into()),
                "bvneg" => Ok(as_bv_unary("bvneg")?.bvneg().into()),

                // N-ary arithmetic
                "bvadd" => {
                    let mut xs = as_bv_list(2, "bvadd")?;
                    let mut acc = xs.remove(0);
                    for x in xs { acc = acc.bvadd(&x); }
                    Ok(acc.into())
                }
                "bvsub" => {
                    let xs = as_bv_list(2, "bvsub")?;
                    let mut it = xs.into_iter();
                    let mut acc = it.next().unwrap();
                    for x in it { acc = acc.bvsub(&x); }
                    Ok(acc.into())
                }
                "bvmul" => {
                    let mut xs = as_bv_list(2, "bvmul")?;
                    let mut acc = xs.remove(0);
                    for x in xs { acc = acc.bvmul(&x); }
                    Ok(acc.into())
                }
                "bvudiv" => {
                    let (a,b) = as_bv_pair("bvudiv")?;
                    Ok(a.bvudiv(&b).into())
                }
                "bvsdiv" => {
                    let (a,b) = as_bv_pair("bvsdiv")?;
                    Ok(a.bvsdiv(&b).into())
                }
                "bvurem" => {
                    let (a,b) = as_bv_pair("bvurem")?;
                    Ok(a.bvurem(&b).into())
                }
                "bvsrem" => {
                    let (a,b) = as_bv_pair("bvsrem")?;
                    Ok(a.bvsrem(&b).into())
                }

                // Shifts
                "bvshl" => {
                    let (a,b) = as_bv_pair("bvshl")?;
                    Ok(a.bvshl(&b).into())
                }
                "bvlshr" => {
                    let (a,b) = as_bv_pair("bvlshr")?;
                    Ok(a.bvlshr(&b).into())
                }
                "bvashr" => {
                    let (a,b) = as_bv_pair("bvashr")?;
                    Ok(a.bvashr(&b).into())
                }

                // Concatenation (left fold)
                "concat" => {
                    let mut xs = as_bv_list(2, "concat")?;
                    let mut acc = xs.remove(0);
                    for x in xs { acc = acc.concat(&x); }
                    Ok(acc.into())
                }

                // Unsigned comparisons
                "bvult" => { let (a,b)=as_bv_pair("bvult")?; Ok(a.bvult(&b).into()) }
                "bvule" => { let (a,b)=as_bv_pair("bvule")?; Ok(a.bvule(&b).into()) }
                "bvugt" => { let (a,b)=as_bv_pair("bvugt")?; Ok(a.bvugt(&b).into()) }
                "bvuge" => { let (a,b)=as_bv_pair("bvuge")?; Ok(a.bvuge(&b).into()) }

                // Signed comparisons
                "bvslt" => { let (a,b)=as_bv_pair("bvslt")?; Ok(a.bvslt(&b).into()) }
                "bvsle" => { let (a,b)=as_bv_pair("bvsle")?; Ok(a.bvsle(&b).into()) }
                "bvsgt" => { let (a,b)=as_bv_pair("bvsgt")?; Ok(a.bvsgt(&b).into()) }
                "bvsge" => { let (a,b)=as_bv_pair("bvsge")?; Ok(a.bvsge(&b).into()) }

                // If you later need extensions/rotates, add:
                // "(_ zero_extend k)" / "(_ sign_extend k)" / "rotate_left" / "rotate_right"
                // by enhancing `parse_expr` to parse those heads and handling here.

                other => Err(format!("Unexpected raw App({}) after inlining; unsupported operator", other)),
            }
        }
    }
}

// ---------------------------
// ITE decomposition
// ---------------------------

fn collect_ite_pairs(e: &Expr) -> Vec<(Expr, Expr)> {
    fn go(e: &Expr, path: Expr, out: &mut Vec<(Expr, Expr)>) {
        match e {
            Expr::Ite(c, t, f) => {
                let g_then = Expr::And(vec![path.clone(), (*c.clone())]);
                let g_else = Expr::And(vec![path, Expr::Not(Box::new((*c.clone())))]);
                go(t, g_then, out);
                go(f, g_else, out);
            }
            _ => out.push((Expr::And(vec![path, Expr::BoolConst(true)]), e.clone())), // normalize
        }
    }
    let mut out = Vec::new();
    go(e, Expr::BoolConst(true), &mut out);
    out
}


fn simplify_guard(e: Expr) -> Expr {
    // Tiny normalizer: and(true, X) => X; and() => true; or() => false; not(not x) => x
    match e {
        Expr::And(mut xs) => {
            let mut flat = Vec::new();
            for x in xs.drain(..) {
                match simplify_guard(x) {
                    Expr::BoolConst(true) => {}
                    Expr::And(inner) => flat.extend(inner),
                    y => flat.push(y),
                }
            }
            if flat.is_empty() { Expr::BoolConst(true) } else if flat.len()==1 { flat.remove(0) } else { Expr::And(flat) }
        }
        Expr::Or(mut xs) => {
            let mut flat = Vec::new();
            for x in xs.drain(..) {
                match simplify_guard(x) {
                    Expr::BoolConst(false) => {}
                    Expr::Or(inner) => flat.extend(inner),
                    y => flat.push(y),
                }
            }
            if flat.is_empty() { Expr::BoolConst(false) } else if flat.len()==1 { flat.remove(0) } else { Expr::Or(flat) }
        }
        Expr::Not(x) => {
            match *x {
                Expr::Not(xx) => simplify_guard(*xx),
                other => Expr::Not(Box::new(simplify_guard(other))),
            }
        }
        other => other,
    }
}

// ---------------------------
// Top-level: build SMVEnv
// ---------------------------

fn leak_str(s: &str) -> &'static str { Box::leak(s.to_string().into_boxed_str()) }

pub fn build_env_from_flat_smt<'ctx>(ctx: &'ctx Context, smt: &str) -> Result<SMVEnv<'ctx>, String> {
    let sexps = parse_sexps(smt)?;

    struct Decl { name: String, sort: Sort }
    struct NextDef { var: String, ret: Sort, body: Expr }
    struct InitDef { var: String, ret: Sort, body: Expr }

    let mut decls: Vec<Decl> = Vec::new();
    let mut fns:   FnTable   = IndexMap::new();
    let mut nexts: Vec<NextDef> = Vec::new();
    let mut inits: Vec<InitDef> = Vec::new();

    for top in sexps {
        let items = match top { SExp::List(v) => v, _ => continue };
        if items.is_empty() { continue; }
        let head = match &items[0] { SExp::Atom(a) => a.as_str(), _ => continue };

        match head {
            "declare-const" => {
                if items.len() != 3 { return Err("declare-const arity".into()); }
                let name = strip_pipes(&items[1].as_atom().ok_or("declare-const name")?);
                let sort = parse_sort(&items[2])?;
                decls.push(Decl { name, sort });
            }
            "define-fun" => {
                if items.len() != 5 { return Err("define-fun arity".into()); }
                let raw = strip_pipes(&items[1].as_atom().ok_or("define-fun name")?);

                // params: list of (name, sort)
                let mut params = Vec::new();
                let param_list = match &items[2] { SExp::List(v) => v, _ => return Err("params must be list".into()) };
                for p in param_list {
                    let pair = match p { SExp::List(v) => v, _ => return Err("param pair".into()) };
                    if pair.len() != 2 { return Err("param pair arity".into()); }
                    let pname = strip_pipes(&pair[0].as_atom().ok_or("param name")?);
                    let psort = parse_sort(&pair[1])?;
                    params.push((pname, psort));
                }

                let ret = parse_sort(&items[3])?;
                let body = parse_expr(&items[4])?;

                if raw.starts_with("next ") {
                    nexts.push(NextDef { var: raw["next ".len()..].to_string(), ret, body });
                } else if raw.starts_with("init ") {
                    inits.push(InitDef { var: raw["init ".len()..].to_string(), ret, body });
                } else {
                    // helper
                    fns.insert(raw, FnDef { params, ret, body });
                }
            }
            _ => {}
        }
    }

    // Build env & auto-bounds for BV (signed full range to match bvsge/bvsle in your env)
    let mut env = SMVEnv::new(ctx);
    for d in &decls {
        let nm: &'static str = leak_str(&d.name);
        match d.sort {
            Sort::Bool => env.register_variable(nm, VarType::Bool { init: None }),
            Sort::Int  => env.register_variable(nm, VarType::Int  { init: None, lower: None, upper: None }),
            Sort::BV(w) => {
                // Unsigned domain: [0, 2^w - 1]. Only set upper when it fits in i64.
                let lo = Some(0i64);
                let hi = if w <= 63 {
                    Some(((1u128 << w) - 1) as i64) // fits up to 2^63-1
                } else {
                    None // leave unbounded if it wouldn't fit into i64
                };
                env.register_variable(nm, VarType::BVector { width: w, lower: lo, upper: hi, init: None });
            }
        }
        
    }

    // Apply INITs (still expect constants)
    for i in &inits {
        let nm: &'static str = leak_str(&i.var);
        let vt = env.get_variable_type(nm).ok_or_else(|| format!("init for undeclared {}", i.var))?.clone();
        match (vt, &i.ret) {
            (VarType::Bool{..}, Sort::Bool) => {
                let val = match &i.body { Expr::BoolConst(b) => *b, _ => return Err(format!("init {} must be Bool const", i.var)) };
                if let Some(v) = env.get_variable_mut(nm) {
                    *v = Variable { sort: VarType::Bool { init: Some(vec![val]) } };
                }
            }
            (VarType::Int{..}, Sort::Int) => {
                let val = match &i.body { Expr::IntConst(k) => *k, _ => return Err(format!("init {} must be Int const", i.var)) };
                if let Some(v) = env.get_variable_mut(nm) {
                    *v = Variable { sort: VarType::Int { init: Some(vec![val]), lower: None, upper: None } };
                }
            }
            (VarType::BVector{width, ..}, Sort::BV(_)) => {
                let bits = match &i.body { Expr::BVConst{bits} => bits.clone(), _ => return Err(format!("init {} must be BV const", i.var)) };
                // convert to i64
                let bv = bv_from_bits(ctx, &bits);
                let as_u = bv.as_u64().unwrap_or(0);
                if let Some(v) = env.get_variable_mut(nm) {
                    *v = Variable { sort: VarType::BVector { width, lower: v.sort_lower(), upper: v.sort_upper(), init: Some(vec![as_u as i64]) } };
                }
            }
            _ => return Err(format!("init {} sort mismatch", i.var)),
        }
    }

    // Helper to re-use existing bounds when overwriting Variable
    trait BoundsExt { fn sort_lower(&self) -> Option<i64>; fn sort_upper(&self) -> Option<i64>; }
    impl BoundsExt for Variable {
        fn sort_lower(&self) -> Option<i64> { match self.sort { VarType::BVector{lower, ..} => lower, _ => None } }
        fn sort_upper(&self) -> Option<i64> { match self.sort { VarType::BVector{upper, ..} => upper, _ => None } }
    }

    // Register transitions from NEXT defs:
    //  - inline helpers in the next-body
    //  - decompose ITEs into (guard, rhs) pairs
    //  - for each pair, register_transition(var, guard, update)
    for n in &nexts {
        let var_nm: &'static str = leak_str(&n.var);
    
        // 1) Inline helpers on-demand with memoization (fast & shared)
        let mut memo = InlineMemo::default();
        let inlined = inline_helpers_memo(&n.body, &fns, &mut memo)?;
    
        // 2) Decompose into disjoint (guard, rhs) pairs
        let pairs = collect_ite_pairs_smart(&inlined);
    
        // 3) Register each pair as a transition (guards/updates are arbitrary ASTs)
        // 3) Print & register each pair as a transition (guards/updates are arbitrary ASTs)
        {
            // Create a stable dummy state once per target variable (nice names for printing)
            let dbg_state = env.make_dummy_state(ctx);

            for (rule_idx, (g_expr, rhs_expr)) in pairs.into_iter().enumerate() {
                // --- DEBUG: compile to Z3 and print before registering ---
                let g_dyn = match expr_to_ast(&g_expr, ctx, &dbg_state) {
                    Ok(x) => x,
                    Err(e) => {
                        eprintln!(
                            "[IR DEBUG] Guard compile error for `{}` rule {}: {}\n  LHS expr: {}",
                            var_nm, rule_idx, e, fmt_expr(&g_expr)
                        );
                        panic!("guard translation failed");
                    }
                };
                let g_bool = match g_dyn.as_bool() {
                    Some(b) => b,
                    None => {
                        eprintln!(
                            "[IR DEBUG] Guard is not Bool for `{}` rule {}.\n  LHS expr: {}",
                            var_nm, rule_idx, fmt_expr(&g_expr)
                        );
                        panic!("guard must be Bool");
                    }
                };

                let rhs_dyn = match expr_to_ast(&rhs_expr, ctx, &dbg_state) {
                    Ok(x) => x,
                    Err(e) => {
                        eprintln!(
                            "[IR DEBUG] Update compile error for `{}` rule {}: {}\n  RHS expr: {}",
                            var_nm, rule_idx, e, fmt_expr(&rhs_expr)
                        );
                        panic!("rhs translation failed");
                    }
                };

                // Print the actual Z3 ASTs
                println!(
                    "[IR DEBUG] {}[{}]: Guard ='{}' -> Update = '{}'",
                    var_nm,
                    rule_idx,
                    g_bool.to_string(),
                    rhs_dyn.to_string()
                );

                // --- Register transition (same closures as before) ---
                let g_expr_cloned = g_expr.clone();
                let rhs_expr_cloned = rhs_expr.clone();
                let var_label = var_nm;

                env.register_transition(
                    var_nm,
                    move |_env, ctx, st| {
                        let g_dyn = match expr_to_ast(&g_expr_cloned, ctx, st) {
                            Ok(x) => x,
                            Err(e) => {
                                eprintln!(
                                    "IR error compiling guard (lhs) for variable `{}`: {}\n  LHS expr: {}",
                                    var_label, e, fmt_expr(&g_expr_cloned)
                                );
                                panic!("guard translation failed");
                            }
                        };
                        let g_bool = match g_dyn.as_bool() {
                            Some(b) => b,
                            None => {
                                eprintln!(
                                    "IR error: guard (lhs) is not Bool for variable `{}`.\n  LHS expr: {}",
                                    var_label, fmt_expr(&g_expr_cloned)
                                );
                                panic!("guard must be Bool");
                            }
                        };
                        ReturnType::DynAst(g_bool.into())
                    },
                    move |_env, ctx, st| {
                        let dyn_ast = match expr_to_ast(&rhs_expr_cloned, ctx, st) {
                            Ok(x) => x,
                            Err(e) => {
                                eprintln!(
                                    "IR error compiling update (rhs) for variable `{}`: {}\n  RHS expr: {}",
                                    var_label, e, fmt_expr(&rhs_expr_cloned)
                                );
                                panic!("rhs translation failed");
                            }
                        };
                        ReturnType::DynAst(dyn_ast)
                    }
                );
            }
        } // dbg_state drops here


        // NOTE: We do NOT rely on stutter default; the pairs cover all cases from the ITEs.
    }
    Ok(env)
}


fn fmt_expr(e: &Expr) -> String {
    fn join(xs: &[String]) -> String { xs.join(" ") }
    match e {
        Expr::Sym(s) => s.clone(),
        Expr::BoolConst(b) => if *b { "true".into() } else { "false".into() },
        Expr::IntConst(i) => i.to_string(),
        Expr::BVConst { bits } => format!("#b{}", bits),
        Expr::Eq(a,b) => format!("(= {} {})", fmt_expr(a), fmt_expr(b)),
        Expr::Ite(c,t,f) => format!("(ite {} {} {})", fmt_expr(c), fmt_expr(t), fmt_expr(f)),
        Expr::Extract { hi, lo, e } =>
            format!("((_ extract {} {}) {})", hi, lo, fmt_expr(e)),
        Expr::And(xs) => format!("(and {})", join(&xs.iter().map(fmt_expr).collect::<Vec<_>>())),
        Expr::Or(xs)  => format!("(or {})",  join(&xs.iter().map(fmt_expr).collect::<Vec<_>>())),
        Expr::Not(x)  => format!("(not {})", fmt_expr(x)),
        Expr::Xor(xs)   => format!("(xor {})",   join(&xs.iter().map(fmt_expr).collect::<Vec<_>>())),
        Expr::BVXor(xs) => format!("(bvxor {})", join(&xs.iter().map(fmt_expr).collect::<Vec<_>>())),
        Expr::App(name, args) =>
            format!("({} {})", name, join(&args.iter().map(fmt_expr).collect::<Vec<_>>())),
    }
}



use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

// ---------- Structural fingerprint (no trait impls needed) ----------
fn fp_u64(mut h: u64, x: u64) -> u64 { // FNV-1a style mix (simple and fast)
    const P: u64 = 0x100000001b3;
    h ^= x;
    h = h.wrapping_mul(P);
    h
}
fn fp_bytes(mut h: u64, bs: &[u8]) -> u64 {
    for &b in bs { h = fp_u64(h, b as u64); }
    h
}
fn fingerprint_expr(e: &Expr) -> u64 {
    fn go(h: u64, e: &Expr) -> u64 {
        match e {
            Expr::Sym(s)           => fp_bytes(fp_u64(h, 1), s.as_bytes()),
            Expr::BoolConst(b)     => fp_u64(fp_u64(h, 2), *b as u64),
            Expr::IntConst(i)      => fp_u64(fp_u64(h, 3), *i as u64),
            Expr::BVConst{bits}    => fp_bytes(fp_u64(h, 4), bits.as_bytes()),
            Expr::Eq(a,b)          => { let h=fp_u64(h,5); let h=go(h,a); go(h,b) }
            Expr::Ite(c,t,f)       => { let h=fp_u64(h,6); let h=go(h,c); let h=go(h,t); go(h,f) }
            Expr::Extract{hi,lo,e} => { let h=fp_u64(h,7); let h=fp_u64(h,*hi as u64); let h=fp_u64(h,*lo as u64); go(h,e) }
            Expr::And(xs)          => { let mut h=fp_u64(h,8); for x in xs { h=go(h,x); } h }
            Expr::Or(xs)           => { let mut h=fp_u64(h,9); for x in xs { h=go(h,x); } h }
            Expr::Not(x)           => go(fp_u64(h,10), x),
            Expr::Xor(xs)          => { let mut h=fp_u64(h,12); for x in xs { h=go(h,x); } h }
            Expr::BVXor(xs)        => { let mut h=fp_u64(h,13); for x in xs { h=go(h,x); } h }
            Expr::App(n,args)      => { let mut h=fp_bytes(fp_u64(h,11), n.as_bytes()); for a in args { h=go(h,a); } h }
        }
    }
    go(0xcbf29ce484222325, e)
}


// ---------- Memoized helper inliner (apps → bodies), high-performance ----------


fn inline_helpers_memo(e: &Expr, fns: &FnTable, memo: &mut InlineMemo) -> Result<Expr, String> {
    match e {
        Expr::App(name, args) if fns.contains_key(name) => {
            // Inline args first (and memoize them implicitly via recursion)
            let mut inlined_args = Vec::with_capacity(args.len());
            let mut arg_fps = Vec::with_capacity(args.len());
            for a in args {
                let a_in = inline_helpers_memo(a, fns, memo)?;
                arg_fps.push(fingerprint_expr(&a_in));
                inlined_args.push(a_in);
            }
            let key: InlineKey = (name.clone(), arg_fps);
            if let Some(cached) = memo.get(&key) { return Ok(cached.clone()); }

            let def = &fns[name];
            if def.params.len() != inlined_args.len() {
                return Err(format!("arity mismatch in call {}: expected {}, got {}",
                                   name, def.params.len(), inlined_args.len()));
            }
            // Build substitution env and substitute
            let mut sub = IndexMap::new();
            for ((p,_ps), a) in def.params.iter().zip(inlined_args.into_iter()) {
                sub.insert(p.clone(), a);
            }
            let body = subst_expr(&def.body, &sub);
            // Recurse: there may be nested helper calls
            let body_in = inline_helpers_memo(&body, fns, memo)?;
            memo.insert(key, body_in.clone());
            Ok(body_in)
        }
        // Non-app nodes: recurse
        Expr::Eq(a,b) => Ok(Expr::Eq(
            Box::new(inline_helpers_memo(a,fns,memo)?),
            Box::new(inline_helpers_memo(b,fns,memo)?),
        )),
        Expr::Ite(c,t,f) => Ok(Expr::Ite(
            Box::new(inline_helpers_memo(c,fns,memo)?),
            Box::new(inline_helpers_memo(t,fns,memo)?),
            Box::new(inline_helpers_memo(f,fns,memo)?),
        )),
        Expr::Extract{hi,lo,e} => Ok(Expr::Extract{
            hi:*hi, lo:*lo,
            e: Box::new(inline_helpers_memo(e,fns,memo)?)
        }),
        Expr::And(xs) => {
            let mut out = Vec::with_capacity(xs.len());
            for x in xs { out.push(inline_helpers_memo(x, fns, memo)?); }
            Ok(Expr::And(out))
        }
        Expr::Or(xs) => {
            let mut out = Vec::with_capacity(xs.len());
            for x in xs { out.push(inline_helpers_memo(x, fns, memo)?); }
            Ok(Expr::Or(out))
        }
        Expr::Xor(xs) => {
            let mut out = Vec::with_capacity(xs.len());
            for x in xs { out.push(inline_helpers_memo(x, fns, memo)?); }
            Ok(Expr::Xor(out))
        }
        Expr::BVXor(xs) => {
            let mut out = Vec::with_capacity(xs.len());
            for x in xs { out.push(inline_helpers_memo(x, fns, memo)?); }
            Ok(Expr::BVXor(out))
        }
        Expr::Not(x) => Ok(Expr::Not(Box::new(inline_helpers_memo(x, fns, memo)?))),
        // Leaves & non-helper apps
        _ => Ok(e.clone()),
    }
}

// ---------- Smart ITE decomposition (skips obviously-false branches) ----------
fn collect_ite_pairs_smart(e: &Expr) -> Vec<(Expr, Expr)> {
    fn go(e: &Expr, path: Expr, out: &mut Vec<(Expr, Expr)>) {
        match e {
            Expr::Ite(c, t, f) => {
                let g_then = simplify_guard(Expr::And(vec![path.clone(), (*c.clone())]));
                let g_else = simplify_guard(Expr::And(vec![path, Expr::Not(Box::new((*c.clone())))]));
                // prune trivially-false guards early
                if !matches!(g_then, Expr::BoolConst(false)) { go(t, g_then, out); }
                if !matches!(g_else, Expr::BoolConst(false)) { go(f, g_else, out); }
            }
            _ => {
                // terminal RHS under current guard
                let g = simplify_guard(path);
                if !matches!(g, Expr::BoolConst(false)) {
                    out.push((g, e.clone()));
                }
            }
        }
    }
    let mut out = Vec::new();
    go(e, Expr::BoolConst(true), &mut out);
    out
}
