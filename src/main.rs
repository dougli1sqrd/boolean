#![feature(
    box_syntax,
    box_patterns,
    generic_const_exprs,
    explicit_generic_args_with_impl_trait
)]

use std::fmt;
use std::fmt::Display;

fn main() {
    println!("Hello, world!");

    let lt = less_than::<1>(GenericSymbol('A'), GenericSymbol('B'));
    println!("{}", lt);
    for i in 0..2 {
        for j in 0..2 {
            let sub = substitute(
                GenericSymbol('A'),
                NValue { value: i },
                substitute(GenericSymbol('B'), NValue { value: j }, lt.clone()),
            );
            //println!("{:?}", sub);
            let v = simplify_complete(sub).unwrap();
            println!("{} {} => {:?}", i, j, v);
        }
    }

    let lt = less_than::<2>(GenericSymbol('A'), GenericSymbol('B'));
    println!("{}", lt);

    for i in 0..4 {
        for j in 0..4 {
            let sub = substitute(
                GenericSymbol('A'),
                NValue { value: i },
                substitute(GenericSymbol('B'), NValue { value: j }, lt.clone()),
            );
            //println!("{:?}", sub);
            let v = simplify_complete(sub).unwrap();
            println!("{} {} => {:?}", i, j, v);
        }
    }

    let lt = less_than::<4>(GenericSymbol('A'), GenericSymbol('B'));
    println!("{}", lt);

    let lt = less_than::<6>(GenericSymbol('A'), GenericSymbol('B'));
    println!("{}", lt);

    //let subbed = substitute(GenericSymbol('B'), NValue { value: 47 }, lt);
    let subbed = substitute(GenericSymbol('B'), NValue { value: 47 }, lt);
    println!("substitue:\n{}", subbed);

    let simple = simplify_complete(subbed);
    match simple {
        Ok(v) => println!("simplified:\n{:?}", v),
        Err(ref x) => println!("simplified:\n {}", x),
    }
    let simp = simple.unwrap_err();

    println!("Table:\n");
    let table = truth_table(simp, GenericSymbol('A'));
    match table {
        Ok(t) => {
            for (input, v) in t {
                println!("{} => {:?}", input.value, v);
            }
        }
        Err(x) => {
            println!("Error: {}", x)
        }
    }
    // let multi_and = and_n::<1>(&['A', 'B', 'C'], Expr::Empty);
    // println!("{}", multi_and);
}

trait AsExpr<const N: u16> {
    fn expr(self) -> Expr<N>;
}

impl<const N: u16> AsExpr<N> for char {
    fn expr(self) -> Expr<N> {
        Expr::Const(Symbol(self, 0))
    }
}

impl<const N: u16> AsExpr<N> for Expr<N> {
    fn expr(self) -> Expr<N> {
        self
    }
}

impl<const N: u16> AsExpr<N> for Symbol<N> {
    fn expr(self) -> Expr<N> {
        Expr::Const(self)
    }
}

impl<const N: u16> AsExpr<N> for (char, u16) {
    fn expr(self) -> Expr<N> {
        Expr::Const(Symbol(self.0, self.1))
    }
}

#[derive(Debug, Copy, Clone, PartialEq)]
struct Symbol<const N: u16>(char, u16);

#[derive(Debug, Copy, Clone, PartialEq)]
struct GenericSymbol<const N: u16>(char);

impl<const N: u16> GenericSymbol<N> {
    fn bit(&self, n: u16) -> Symbol<N> {
        Symbol(self.0, n)
    }

    fn all_bits(&self) -> [Symbol<N>; N as usize] where {
        let mut bits = [Symbol(' ', 0); N as usize];
        for i in 0..N {
            bits[i as usize] = self.bit(i)
        }
        bits
    }
}

#[derive(Debug, Clone, PartialEq)]
enum Expr<const N: u16> {
    Empty,
    Value(Value),
    Const(Symbol<N>),
    And(Box<Expr<N>>, Box<Expr<N>>),
    Or(Box<Expr<N>>, Box<Expr<N>>),
    Xor(Box<Expr<N>>, Box<Expr<N>>),
    Not(Box<Expr<N>>),
}

#[derive(Debug, Clone, PartialEq, Copy)]
enum Value {
    True,
    False,
}

#[derive(Debug, Clone, PartialEq, Copy)]
struct NValue<const N: u16> {
    value: u16,
}

impl<const N: u16> NValue<N> {
    fn new(value: u16) -> NValue<N> {
        NValue { value }
    }
}

impl<const N: u16> NValue<N> {
    fn bit(&self, n: u16) -> Value {
        if (self.value & (1 << n)) != 0 {
            Value::True
        } else {
            Value::False
        }
    }
}

impl<const N: u16> Display for Expr<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            Expr::Empty => format!(""),
            Expr::Value(v) => format!("{:?}", v),
            Expr::Const(Symbol(c, n)) => format!("{}_{}", c, n),
            Expr::Not(expr) => match **expr {
                Expr::Const(_) => format!("! {}", expr),
                Expr::Value(_) => format!("! {}", expr),
                _ => format!("! ({})", expr),
            },
            Expr::And(a, b) => match (*a.clone(), *b.clone()) {
                (Expr::Const(_), Expr::Const(_)) => format!("{} * {}", a, b),
                (Expr::Const(_), Expr::Not(box Expr::Const(_))) => format!("{} * {}", a, b),
                (Expr::Const(_), _) => format!("{} * ({})", a, b),
                (Expr::Not(box Expr::Const(_)), Expr::Const(_)) => format!("{} * {}", a, b),
                (Expr::Not(box Expr::Const(_)), Expr::Not(box Expr::Const(_))) => {
                    format!("{} * {}", a, b)
                }
                (_, Expr::Const(_)) => format!("({}) * {}", a, b),
                (_, _) => format!("({}) * ({})", a, b),
            },
            Expr::Or(a, b) => match (*a.clone(), *b.clone()) {
                (Expr::Const(_), Expr::Const(_)) => format!("{} + {}", a, b),
                (Expr::Const(_), Expr::Not(box Expr::Const(_))) => format!("{} + {}", a, b),
                (Expr::Const(_), _) => format!("{} + ({})", a, b),
                (Expr::Not(box Expr::Const(_)), Expr::Const(_)) => format!("{} + {}", a, b),
                (Expr::Not(box Expr::Const(_)), Expr::Not(box Expr::Const(_))) => {
                    format!("{} + {}", a, b)
                }
                (_, Expr::Const(_)) => format!("({}) + {}", a, b),
                (_, _) => format!("({}) + ({})", a, b),
            },
            Expr::Xor(a, b) => match (*a.clone(), *b.clone()) {
                (Expr::Const(_), Expr::Const(_)) => format!("{} ^ {}", a, b),
                (Expr::Const(_), Expr::Not(box Expr::Const(_))) => format!("{} ^ {}", a, b),
                (Expr::Const(_), _) => format!("{} ^ ({})", a, b),
                (Expr::Not(box Expr::Const(_)), Expr::Const(_)) => format!("{} ^ {}", a, b),
                (Expr::Not(box Expr::Const(_)), Expr::Not(box Expr::Const(_))) => {
                    format!("{} ^ {}", a, b)
                }
                (_, Expr::Const(_)) => format!("({}) ^ {}", a, b),
                (_, _) => format!("({}) ^ ({})", a, b),
            },
        };
        write!(f, "{}", s)
    }
}

fn simplify<const N: u16>(expr: Expr<N>) -> Expr<N> {
    match expr {
        Expr::Empty => Expr::Empty,
        Expr::Value(v) => Expr::Value(v),
        Expr::Const(c) => Expr::Const(c),
        Expr::Not(v) => match *v {
            Expr::Value(Value::True) => Expr::Value(Value::False),
            Expr::Value(Value::False) => Expr::Value(Value::True),
            _ => Expr::Not(Box::new(simplify(*v))),
        },
        Expr::And(a, b) => match (*a.clone(), *b.clone()) {
            (Expr::Value(Value::True), x) => simplify(x),
            (x, Expr::Value(Value::True)) => simplify(x),
            (Expr::Value(Value::False), _) => Expr::Value(Value::False),
            (_, Expr::Value(Value::False)) => Expr::Value(Value::False),
            (_, _) => Expr::And(Box::new(simplify(*a)), Box::new(simplify(*b))),
        },
        Expr::Or(a, b) => match (*a.clone(), *b.clone()) {
            (Expr::Value(Value::True), _) => Expr::Value(Value::True),
            (_, Expr::Value(Value::True)) => Expr::Value(Value::True),
            (Expr::Value(Value::False), x) => simplify(x),
            (x, Expr::Value(Value::False)) => simplify(x),
            (_, _) => Expr::Or(Box::new(simplify(*a)), Box::new(simplify(*b))),
        },
        Expr::Xor(a, b) => match (*a.clone(), *b.clone()) {
            (Expr::Value(Value::False), Expr::Value(Value::False)) => Expr::Value(Value::False),
            (Expr::Value(Value::True), Expr::Value(Value::True)) => Expr::Value(Value::False),
            (Expr::Value(_), Expr::Value(_)) => Expr::Value(Value::True),
            (_, _) => Expr::Xor(Box::new(simplify(*a)), Box::new(simplify(*b))),
        },
    }
}

fn sub_one<const N: u16>(x: Symbol<N>, v: Value, expr: Expr<N>) -> Expr<N> {
    match expr {
        Expr::Const(c) => {
            if c == x {
                Expr::Value(v)
            } else {
                Expr::Const(c)
            }
        }
        Expr::Not(a) => Expr::Not(Box::new(sub_one(x, v, *a))),
        Expr::And(a, b) => Expr::And(Box::new(sub_one(x, v, *a)), Box::new(sub_one(x, v, *b))),
        Expr::Or(a, b) => Expr::Or(Box::new(sub_one(x, v, *a)), Box::new(sub_one(x, v, *b))),
        Expr::Xor(a, b) => Expr::Xor(Box::new(sub_one(x, v, *a)), Box::new(sub_one(x, v, *b))),
        p => p,
    }
}

fn substitute<const N: u16>(x: GenericSymbol<N>, v: NValue<N>, expr: Expr<N>) -> Expr<N> {
    let mut exp = expr;
    for n in 0..N {
        exp = sub_one(x.bit(n), v.bit(n), exp);
    }
    exp
}

fn xor<const N: u16>(a: impl AsExpr<N>, b: impl AsExpr<N>) -> Expr<N> {
    Expr::Xor(Box::new(a.expr().clone()), Box::new(b.expr().clone()))
}

fn _xor<const N: u16>(a: &Expr<N>, b: &Expr<N>) -> Expr<N> {
    Expr::Or(
        Box::new(Expr::And(
            Box::new(Expr::Not(Box::new(a.clone()))),
            Box::new(b.clone()),
        )),
        Box::new(Expr::And(
            Box::new(a.clone()),
            Box::new(Expr::Not(Box::new(b.clone()))),
        )),
    )
}

fn and<const N: u16>(a: impl AsExpr<N>, b: impl AsExpr<N>) -> Expr<N> {
    Expr::And(Box::new(a.expr()), Box::new(b.expr()))
}

/// Multi input And
/// A1 * A2 * ... * AN => A1 * (A2 * ( ... * AN))
fn and_n<const N: u16>(exprs: &[impl AsExpr<N> + Clone], current: Expr<N>) -> Expr<N> {
    if exprs.len() == 0 {
        current
    } else if exprs.len() == 1 {
        let a = exprs[0].clone().expr();
        if current == Expr::Empty {
            a
        } else {
            and(current, a)
        }
    } else {
        if current == Expr::Empty {
            let a = exprs[0].clone().expr();
            let b = exprs[1].clone().expr();
            and_n(&exprs[2..], and(a, b))
        } else {
            let a = exprs[0].clone().expr();
            and_n(&exprs[1..], and(current, a))
        }
    }
}

/// Multi input Or
/// A1 * A2 * ... * AN => A1 * (A2 * ( ... * AN))
fn or_n<const N: u16>(exprs: &[impl AsExpr<N> + Clone], current: Expr<N>) -> Expr<N> {
    if exprs.len() == 0 {
        current
    } else {
        if current == Expr::Empty {
            let a = exprs[0].clone().expr();
            let b = exprs[1].clone().expr();
            and_n(&exprs[2..], or(a, b))
        } else {
            let a = exprs[0].clone().expr();
            and_n(&exprs[1..], or(a, current))
        }
    }
}

fn or<const N: u16>(a: impl AsExpr<N>, b: impl AsExpr<N>) -> Expr<N> {
    Expr::Or(Box::new(a.expr()), Box::new(b.expr()))
}

fn not<const N: u16>(a: impl AsExpr<N>) -> Expr<N> {
    Expr::Not(Box::new(a.expr()))
}

/// A == B
/// (A == B) = (A_0 xor B_0) (A_1 xor B_1) (A_2 xor B_2) (A_3 xor B_3)
fn equal_to<const N: u16>(a: GenericSymbol<N>, b: GenericSymbol<N>) -> Expr<N> {
    prod_of_xnor(a, b, 0)
}

fn prod_of_xnor<const N: u16>(a: GenericSymbol<N>, b: GenericSymbol<N>, to: u16) -> Expr<N> {
    let mut zipped = Vec::new();
    for i in to..N {
        zipped.push(not(xor(a.bit(i), b.bit(i))));
    }
    and_n(&zipped, Expr::Empty)
}

/// Boolean expression of N inputs for A < B
/// !A_3 * B_3 + (A_3 xor B_3) * !A_2 * B_2 + (A_3 xor B_3) * (A_2 xor B_2) * !A_1 * B_1 + (A_3 xor B_3) * (A_2 xor B_2) * (A_1 xor B_1) * !A_0 * B_0
fn less_than<const N: u16>(a: GenericSymbol<N>, b: GenericSymbol<N>) -> Expr<N> {
    let mut expr = and(not(a.bit(N - 1)), b.bit(N - 1));
    for n in (0..(N - 1)).rev() {
        expr = or(
            expr,
            and(prod_of_xnor(a, b, n + 1), and(not(a.bit(n)), b.bit(n))),
        )
    }
    expr
}

fn greater_than<const N: u16>(a: GenericSymbol<N>, b: GenericSymbol<N>) -> Expr<N> {
    if true {
        panic!("not fixed yet")
    }
    let mut expr = Expr::Empty;
    for i in 0..N {
        let n = N - 1 - i;
        if expr == Expr::Empty {
            expr = and(a.bit(n), not(b.bit(n)));
        } else {
            expr = or(
                expr,
                and(prod_of_xnor(a, b, n), and(a.bit(n), not(b.bit(n)))),
            )
        }
    }
    expr
}

fn greater_than_or_equal_to<const N: u16>(a: GenericSymbol<N>, b: GenericSymbol<N>) -> Expr<N> {
    or(greater_than(a, b), equal_to(a, b))
}

fn truth_table<const N: u16>(
    expr: Expr<N>,
    symbol: GenericSymbol<N>,
) -> Result<Vec<(NValue<N>, Value)>, Expr<N>> {
    let mut table: Vec<(NValue<N>, Value)> = Vec::new();
    for i in 0..2_u16.pow(N.into()) {
        let value: NValue<N> = NValue::new(i);
        let sub = substitute(symbol, value, expr.clone());
        let simplified = simplify_complete(sub);
        match simplified {
            Ok(v) => table.push((value, v)),
            Err(x) => return Err(x),
        }
    }

    Ok(table)
}

fn simplify_complete<const N: u16>(expr: Expr<N>) -> Result<Value, Expr<N>> {
    let simp = simplify(expr.clone());
    if simp == expr {
        // If they're equal, then it is simplified
        match simp {
            Expr::Value(v) => Ok(v),
            _ => Err(simp),
        }
    } else {
        simplify_complete(simp)
    }
}
