use crate::definitions::*;


// ***************** Formula to Expression *****************
/// Check if two expressions are the same.
pub fn identity(a: &Expression, b: &Expression) -> bool {
    match (a, b) {
        (Expression::True, Expression::True) => true,
        (Expression::False, Expression::False) => true,
        (Expression::Literal(Literal::Atom(v)), Expression::Literal(Literal::Atom(w))) => v == w,
        (Expression::Literal(Literal::NegAtom(v)), Expression::Literal(Literal::NegAtom(w))) => v == w,
        (Expression::Neg(a), Expression::Neg(b)) => identity(a, b),
        (Expression::And(a1, b1), Expression::And(a2, b2)) => identity(a1, a2) && identity(b1, b2),
        (Expression::Or(a1, b1), Expression::Or(a2, b2)) => identity(a1, a2) && identity(b1, b2),
        (Expression::Implies(a1, b1), Expression::Implies(a2, b2)) => identity(a1, a2) && identity(b1, b2),
        (Expression::Iff(a1, b1), Expression::Iff(a2, b2)) => identity(a1, a2) && identity(b1, b2),
        (Expression::MOr(xs), Expression::MOr(ys)) => {
            if xs.len() != ys.len() {
                false
            } else {
                xs.iter().zip(ys).all(|(x, y)| identity(x, y))
            }
        }
        (Expression::MAnd(xs), Expression::MAnd(ys)) => {
            if xs.len() != ys.len() {
                false
            } else {
                xs.iter().zip(ys).all(|(x, y)| identity(x, y))
            }
        }
        _ => false,
    }
}

/// Convert a disjunctive formula to an expression.
pub fn disjunctive_formula_toexpr(d: DisjunctiveFormula) -> Expression {
    match d {
        DisjunctiveFormula::TrueDisj => Expression::True,
        DisjunctiveFormula::FalseDisj => Expression::False,
        DisjunctiveFormula::Disj(ls) => match ls.as_slice() {
            [] => Expression::False,
            [a] => Expression::Literal(a.clone()),
            [a, b] => Expression::Or(Box::new(Expression::Literal(a.clone())), Box::new(Expression::Literal(b.clone()))),
            ls => Expression::MOr(ls.iter().map(|l| Expression::Literal(l.clone())).collect()),
        },
    }
}

/// Convert a conjunctive formula to an expression.
pub fn conjunctive_formula_toexpr(c: ConjunctiveFormula) -> Expression {
    match c {
        ConjunctiveFormula::TrueConj => Expression::True,
        ConjunctiveFormula::FalseConj => Expression::False,
        ConjunctiveFormula::Conj(ls) => match ls.as_slice() {
            [] => Expression::True,
            [a] => Expression::Literal(a.clone()),
            [a, b] => Expression::And(Box::new(Expression::Literal(a.clone())), Box::new(Expression::Literal(b.clone()))),
            ls => Expression::MAnd(ls.iter().map(|l| Expression::Literal(l.clone())).collect()),
        },
    }
}

/// Convert a CNF to an expression.
pub fn cnf_to_expression(ds: Vec<DisjunctiveFormula>) -> Expression {
    match ds.as_slice() {
        [] => Expression::False,
        [a] => disjunctive_formula_toexpr(a.clone()),
        [a, b] => Expression::And(Box::new(disjunctive_formula_toexpr(a.clone())), Box::new(disjunctive_formula_toexpr(b.clone()))),
        ls => Expression::MAnd(ls.iter().map(|l| disjunctive_formula_toexpr(l.clone())).collect()),
    }
}

/// Convert a DNF to an expression.
pub fn dnf_to_expression(cs: Vec<ConjunctiveFormula>) -> Expression {
    match cs.as_slice() {
        [] => Expression::True,
        [a] => conjunctive_formula_toexpr(a.clone()),
        [a, b] => Expression::Or(Box::new(conjunctive_formula_toexpr(a.clone())), Box::new(conjunctive_formula_toexpr(b.clone()))),
        ls => Expression::MOr(ls.iter().map(|l| conjunctive_formula_toexpr(l.clone())).collect()),
    }
}


// ***************** Testing *****************
#[cfg(test)]
mod tests {
    use super::*;


    #[test]
    /// Test the identity function.
    fn test_identity() {
        // True, True
        let a = Expression::True;
        let b = Expression::True;
        assert_eq!(identity(&a, &b), true);

        // False, False
        let a = Expression::False;
        let b = Expression::False;
        assert_eq!(identity(&a, &b), true);

        // Atom, Atom (same)
        let a = Expression::Literal(Literal::Atom("a".to_string()));
        let b = Expression::Literal(Literal::Atom("a".to_string()));
        assert_eq!(identity(&a, &b), true);

        // Atom, Atom (different)
        let a = Expression::Literal(Literal::Atom("a".to_string()));
        let b = Expression::Literal(Literal::Atom("b".to_string()));
        assert_eq!(identity(&a, &b), false);

        // NegAtom, NegAtom (same)
        let a = Expression::Literal(Literal::NegAtom("a".to_string()));
        let b = Expression::Literal(Literal::NegAtom("a".to_string()));
        assert_eq!(identity(&a, &b), true);

        // NegAtom, NegAtom (different)
        let a = Expression::Literal(Literal::NegAtom("a".to_string()));
        let b = Expression::Literal(Literal::NegAtom("b".to_string()));
        assert_eq!(identity(&a, &b), false);

        // Neg, Neg (same)
        let a = Expression::Neg(Box::new(Expression::True));
        let b = Expression::Neg(Box::new(Expression::True));
        assert_eq!(identity(&a, &b), true);

        // Or, Or (same)
        let a = Expression::Or(Box::new(Expression::True), Box::new(Expression::False));
        let b = Expression::Or(Box::new(Expression::True), Box::new(Expression::False));
        assert_eq!(identity(&a, &b), true);

        // And, And (same)
        let a = Expression::And(Box::new(Expression::True), Box::new(Expression::False));
        let b = Expression::And(Box::new(Expression::True), Box::new(Expression::False));
        assert_eq!(identity(&a, &b), true);

        // Implies, Implies (same)
        let a = Expression::Implies(Box::new(Expression::True), Box::new(Expression::False));
        let b = Expression::Implies(Box::new(Expression::True), Box::new(Expression::False));
        assert_eq!(identity(&a, &b), true);

        // Iff, Iff (same)
        let a = Expression::Iff(Box::new(Expression::True), Box::new(Expression::False));
        let b = Expression::Iff(Box::new(Expression::True), Box::new(Expression::False));
        assert_eq!(identity(&a, &b), true);

        // MOr, MOr (same)
        let a = Expression::MOr(vec![Expression::True, Expression::False]);
        let b = Expression::MOr(vec![Expression::True, Expression::False]);
        assert_eq!(identity(&a, &b), true);

        // MAnd, MAnd (same)
        let a = Expression::MAnd(vec![Expression::True, Expression::False]);
        let b = Expression::MAnd(vec![Expression::True, Expression::False]);
        assert_eq!(identity(&a, &b), true);

        // MOr, MOr (different)
        let a = Expression::MOr(vec![Expression::True, Expression::False]);
        let b = Expression::MOr(vec![Expression::True, Expression::True]);
        assert_eq!(identity(&a, &b), false);
    }

    #[test]
    /// Test the disjunctive_formula_toexpr function.
    fn test_disjunctive_formula_toexpr() {
        let d = DisjunctiveFormula::Disj(vec![Literal::Atom("a".to_string()), Literal::Atom("b".to_string())]);
        let e = disjunctive_formula_toexpr(d);
        assert_eq!(e, Expression::Or(Box::new(Expression::Literal(Literal::Atom("a".to_string()))), Box::new(Expression::Literal(Literal::Atom("b".to_string())))));
    }

    #[test]
    /// Test the conjunctive_formula_toexpr function.
    fn test_conjunctive_formula_toexpr() {
        let c = ConjunctiveFormula::Conj(vec![Literal::Atom("a".to_string()), Literal::Atom("b".to_string())]);
        let e = conjunctive_formula_toexpr(c);
        assert_eq!(e, Expression::And(Box::new(Expression::Literal(Literal::Atom("a".to_string()))), Box::new(Expression::Literal(Literal::Atom("b".to_string())))));
    }

}


// use crate::definitions::*;
//
//
// // ***************** Formula to Expression *****************
// /// Check if two expressions are the same.
// pub fn identity(a: &Expression, b: &Expression) -> bool {
//     match (a, b) {
//         (Expression::True, Expression::True) => true,
//         (Expression::False, Expression::False) => true,
//         (Expression::Literal(l1), Expression::Literal(l2)) => l1 == l2,
//         (Expression::Neg(a), Expression::Neg(b)) => identity(a, b),
//         (Expression::Or(a1, b1), Expression::Or(a2, b2)) => identity(a1, a2) && identity(b1, b2),
//         (Expression::And(a1, b1), Expression::And(a2, b2)) => identity(a1, a2) && identity(b1, b2),
//         (Expression::Implies(a1, b1), Expression::Implies(a2, b2)) => identity(a1, a2) && identity(b1, b2),
//         (Expression::Iff(a1, b1), Expression::Iff(a2, b2)) => identity(a1, a2) && identity(b1, b2),
//         (Expression::MOr(xs), Expression::MOr(ys)) => {
//             if xs.len() != ys.len() {
//                 false
//             } else {
//                 xs.iter().zip(ys).all(|(x, y)| identity(x, y))
//             }
//         }
//         (Expression::MAnd(xs), Expression::MAnd(ys)) => {
//             if xs.len() != ys.len() {
//                 false
//             } else {
//                 xs.iter().zip(ys).all(|(x, y)| identity(x, y))
//             }
//         }
//         _ => false,
//     }
// }
//
// /// Convert a disjunctive formula to an expression.
// pub fn disjunctive_formula_toexpr(d: &DisjunctiveFormula) -> Expression {
//     match d {
//         DisjunctiveFormula::TrueDisj => Expression::True,
//         DisjunctiveFormula::FalseDisj => Expression::False,
//         DisjunctiveFormula::Disj(ls) => match ls.as_slice() {
//             [] => Expression::False,
//             [a] => Expression::Literal(a),
//             [a, b] => Expression::Or(Box::new(Expression::Literal(a)), Box::new(Expression::Literal(b))),
//             ls => Expression::MOr(ls.iter().map(|l| Expression::Literal(l)).collect()),
//         },
//     }
// }
//
// /// Convert a conjunctive formula to an expression.
// pub fn conjunctive_formula_toexpr(c: &ConjunctiveFormula) -> Expression {
//     match c {
//         ConjunctiveFormula::TrueConj => Expression::True,
//         ConjunctiveFormula::FalseConj => Expression::False,
//         ConjunctiveFormula::Conj(ls) => match ls.as_slice() {
//             [] => Expression::True,
//             [a] => Expression::Literal(a),
//             [a, b] => Expression::And(Box::new(Expression::Literal(a)), Box::new(Expression::Literal(b))),
//             ls => Expression::MAnd(ls.iter().map(|l| Expression::Literal(l)).collect()),
//         },
//     }
// }
//
// /// Convert a CNF to an expression.
// pub fn cnf_to_expression(ds: &Vec<DisjunctiveFormula>) -> Expression {
//     match ds.as_slice() {
//         [] => Expression::False,
//         [a] => disjunctive_formula_toexpr(a),
//         [a, b] => Expression::And(Box::new(disjunctive_formula_toexpr(a)), Box::new(disjunctive_formula_toexpr(b))),
//         ls => Expression::MAnd(ls.iter().map(|l| disjunctive_formula_toexpr(l)).collect()),
//     }
// }
//
// /// Convert a DNF to an expression.
// pub fn dnf_to_expression(cs: &Vec<ConjunctiveFormula>) -> Expression {
//     match cs.as_slice() {
//         [] => Expression::True,
//         [a] => conjunctive_formula_toexpr(a),
//         [a, b] => Expression::Or(Box::new(conjunctive_formula_toexpr(a)), Box::new(conjunctive_formula_toexpr(b))),
//         ls => Expression::MOr(ls.iter().map(|l| conjunctive_formula_toexpr(l)).collect()),
//     }
// }
//
//
// #[cfg(test)]
// mod tests {
//     use super::*;
//     use crate::definitions::Literal;
//
//     #[test]
//     fn test_identity() {
//         let lita = Literal::Atom("a".to_string());
//         let litb = Literal::Atom("b".to_string());
//
//         let a = Expression::True;
//         let b = Expression::True;
//         assert_eq!(identity(&a, &b), true);
//
//         let a = Expression::False;
//         let b = Expression::False;
//         assert_eq!(identity(&a, &b), true);
//
//         let a = Expression::Literal(&lita);
//         let b = Expression::Literal(&lita);;
//         assert_eq!(identity(&a, &b), true);
//
//         let a = Expression::Literal(&lita);
//         let b = Expression::Literal(&litb);
//         assert_eq!(identity(&a, &b), false);
//     }
//
//     #[test]
//     fn test_disjunctive_formula_toexpr() {
//         let d = DisjunctiveFormula::TrueDisj;
//         assert_eq!(disjunctive_formula_toexpr(&d), Expression::True);
//
//         let d = DisjunctiveFormula::FalseDisj;
//         assert_eq!(disjunctive_formula_toexpr(&d), Expression::False);
//
//         let d = DisjunctiveFormula::Disj(vec![Literal::Atom("a".to_string())]);
//         assert_eq!(disjunctive_formula_toexpr(&d), Expression::Literal(&Literal::Atom("a".to_string())));
//     }
// }