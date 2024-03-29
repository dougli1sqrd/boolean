#![feature(
    box_syntax,
    box_patterns,
    generic_const_exprs,
    explicit_generic_args_with_impl_trait
)]

use std::fmt::{self, format};
use std::fmt::Display;

const A: char = 'A';
const B: char = 'B';

fn main() {
    // Visible is (L >= 40) && (L < 440)
    // let vert_greater_than = simplify_complete(
    //     substitute(
    //         GenericSymbol('B'), NValue { value: 40 }, 
    //         greater_than_or_equal_to::<10>(GenericSymbol('A'), GenericSymbol('B'))
    //     )
    // );

    // let vert_less_than = simplify_complete(
    //     substitute(
    //         GenericSymbol('B'), NValue { value: 440 },
    //         less_than::<10>(GenericSymbol('A'), GenericSymbol('B'))
    //     )
    // );
    
    // let vertical_visible = simplify_complete(
    //     and(
    //         vert_greater_than,
    //         vert_less_than
    //     )
    // );
    
    // println!("Vertical Visible ((L >= 40) && (L < 440)):");
    // for (n, value) in truth_table(vertical_visible, GenericSymbol('A')) {
    //     println!("{} => {}", n.value, value);
    // }
    // println!("{}", vertical_visible);

    // V Sync, when L = 490, 491
    // let vsync_start = simplify_complete(
    //     substitute(
    //         GenericSymbol('B'), NValue { value: 490 }, 
    //         equal_to::<10>(GenericSymbol('A'), GenericSymbol('B'))
    //     )
    // );

    // let vsync_end = simplify_complete(
    //     substitute(
    //         GenericSymbol('B'), NValue { value: 491 }, 
    //         equal_to::<10>(GenericSymbol('A'), GenericSymbol('B'))
    //     )
    // );

    // let vsync = simplify_complete(
    //     not(or(
    //         vsync_start,
    //         vsync_end
    //     ))
    // );

    // println!("Vertical Visible NOT (L == 490 OR L == 491):");
    // for (n, value) in truth_table(vsync.clone(), GenericSymbol('A')) {
    //     println!("{} => {}", n.value, value);
    // }

    // println!("{}", vsync);



    // println!("{}", vsync);

    //        2 + ! 3 + 4 + ! 5 + ! 6 + ! 7 + ! 8 + 9

    // ! 1 + (2 + (! 3 + (4 + (! 5 + (! 6 + (! 7 + (! 8 + 9)))))))
    // ! 1 + 2 + ! 3 + 4 + ! 5 + ! 6 + ! 7 + ! 8 + 9
    // let testvsync = or::<10>(
    //     not(Expr::Const(Symbol(A, 1))),
    //     or(
    //         Expr::Const(Symbol(A, 2)),
    //         or(
    //             not(Expr::Const(Symbol(A, 3))),
    //             or(
    //                 Expr::Const(Symbol(A, 4)),
    //                 or(
    //                     not(Expr::Const(Symbol(A, 5))),
    //                     or(
    //                         not(Expr::Const(Symbol(A, 6))),
    //                         or(
    //                             not(Expr::Const(Symbol(A, 7))),
    //                             or(
    //                                 not(Expr::Const(Symbol(A, 8))),
    //                                 Expr::Const(Symbol(A, 9))
    //                             )
    //                         )
    //                     )
    //                 )
    //             )
    //         )
    //     )
    // );

    // for (n, value) in truth_table(testvsync, GenericSymbol('A')) {
    //     println!("{} => {}", n.value, value);
    // }

    // let end_of_frame = simplify_complete(
    //     substitute(GenericSymbol(B), NValue { value: 525 },
    //         equal_to::<10>(GenericSymbol(A), GenericSymbol(B))
    //     )
    // );

    // for (n, value) in truth_table(end_of_frame, GenericSymbol('A')) {
    //     println!("{} => {}", n.value, value);
    // }

    // println!("{}", end_of_frame);

    // ------------------------------------------------------------------
    // let h_visible = simplify_complete(
    //     substitute(GenericSymbol(B), NValue { value: 640 }, 
    //         less_than::<10>(GenericSymbol(A), GenericSymbol(B))
    //     )
    // );

    // for (n, value) in truth_table(h_visible, GenericSymbol('A')) {
    //     println!("{} => {}", n.value, value);
    // }

    // println!("{}", h_visible);

    // NOT (hsync >= 656) AND (hsync < 752)

    // (hsync >= 656)
    // let hsync_low = simplify_complete(
    //     substitute(GenericSymbol(B), NValue { value: 656 },
    //         greater_than_or_equal_to::<10>(GenericSymbol(A), GenericSymbol(B))
    //     )
    // );
    // // (hsync < 752)
    // let hsync_high = simplify_complete(
    //     substitute(GenericSymbol(B), NValue { value: 752 }, 
    //         less_than::<10>(GenericSymbol(A), GenericSymbol(B))
    //     )
    // );

    // let hsync = not(
    //     and(
    //         hsync_low,
    //         hsync_high
    //     )
    // );

    // for (n, value) in truth_table(hsync, GenericSymbol('A')) {
    //     println!("{} => {}", n.value, value);
    // }

    // println!("{}", hsync);

    let end_line = simplify_complete(
        substitute(GenericSymbol(B), NValue { value: 800 }, 
            equal_to::<10>(GenericSymbol(A), GenericSymbol(B))
        )
    );

    // for (n, value) in truth_table(end_line, GenericSymbol('A')) {
    //     println!("{} => {}", n.value, value);
    // }

    println!("{}", end_line)


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

impl<const N: u16> AsExpr<N> for Box<Expr<N>> {
    fn expr(self) -> Expr<N> {
        *self.clone()
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
                (Expr::Value(_), Expr::Value(_)) => format!("{} * {}", a, b),
                (Expr::Value(_), _) => format!("{} * ({})", a, b),
                (_, Expr::Value(_)) => format!("({}) * {}", a, b),
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
                (Expr::Value(_), Expr::Value(_)) => format!("{} + {}", a, b),
                (Expr::Value(_), _) => format!("{} + ({})", a, b),
                (_, Expr::Value(_)) => format!("({}) + {}", a, b),
                (Expr::Not(box Expr::Const(_)), Expr::Const(_)) => format!("{} + {}", a, b),
                (Expr::Not(box Expr::Const(_)), Expr::Not(box Expr::Const(_))) => {
                    format!("{} + {}", a, b)
                }
                (_, Expr::Const(_)) => format!("({}) + {}", a, b),
                (_, _) => format!("({}) + ({})", a, b),
            },
            Expr::Xor(a, b) => match (*a.clone(), *b.clone()) {
                (Expr::Const(_), Expr::Const(_)) => format!("{} ⊕ {}", a, b),
                (Expr::Const(_), Expr::Not(box Expr::Const(_))) => format!("{} ⊕ {}", a, b),
                (Expr::Const(_), _) => format!("{} ⊕ ({})", a, b),
                (Expr::Value(_), Expr::Value(_)) => format!("{} ⊕ {}", a, b),
                (Expr::Value(_), _) => format!("{} ⊕ ({})", a, b),
                (_, Expr::Value(_)) => format!("({}) ⊕ {}", a, b),
                (Expr::Not(box Expr::Const(_)), Expr::Const(_)) => format!("{} ⊕ {}", a, b),
                (Expr::Not(box Expr::Const(_)), Expr::Not(box Expr::Const(_))) => {
                    format!("{} ⊕ {}", a, b)
                }
                (_, Expr::Const(_)) => format!("({}) ⊕ {}", a, b),
                (_, _) => format!("({}) ⊕ ({})", a, b),
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
            // xor is !a*b + a*!b
            (_, _) => or(
                and(not(a.clone()), b.clone()),
                and(a, not(b))
            )
        },
    }
}

/// Substitute the value v for a single occurance of the symbol x in the expression expr
fn sub_one<const N: u16>(x: Symbol<N>, v: Value, expr: Expr<N>) -> Expr<N> {
    match expr {
        Expr::Const(c) => {
            // If the expression is a symbol c, then substitute c for v if it matches
            // our given symbol x. Otherwise leave it as is.
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
    let mut expr = and(a.bit(N - 1), not(b.bit(N - 1)));
    for n in (0..(N - 1)).rev() {
        expr = or(
            expr,
            and(prod_of_xnor(a, b, n + 1), and(a.bit(n), not(b.bit(n))))
        )
    }
    expr
}

fn greater_than_or_equal_to<const N: u16>(a: GenericSymbol<N>, b: GenericSymbol<N>) -> Expr<N> {
    or(greater_than(a, b), equal_to(a, b))
}

fn truth_table<const N: u16>(
    expr: Expr<N>,
    symbol: GenericSymbol<N>,
) -> Vec<(NValue<N>, Expr<N>)> {
    let mut table: Vec<(NValue<N>, Expr<N>)> = Vec::new();
    for i in 0..2_u16.pow(N.into()) {
        let value: NValue<N> = NValue::new(i);
        let sub = substitute(symbol, value, expr.clone());
        let simplified = simplify_complete(sub);
        table.push((value, simplified));
    }

    table
}

fn simplify_complete<const N: u16>(expr: Expr<N>) -> Expr<N> {
    let simp = simplify(expr.clone());
    if simp == expr {
        // If they're equal, then it is simplified
        return simp
    } else {
        simplify_complete(simp)
    }
}
