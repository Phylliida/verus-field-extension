use crate::poly_arith::{ext_mul, poly_eqv, poly_one};
use verus_algebra::traits::ring::Ring;
use vstd::prelude::*;

verus! {

/// A monic irreducible polynomial p(x) = x^n + c_{n-1}·x^{n-1} + ... + c_0
/// fixed at the type level, used to construct the quotient ring F[x]/(p(x)).
///
/// Analogous to `Radicand` in verus-quadratic-extension, but generalizes from
/// degree 2 (x² - d) to arbitrary degree n ≥ 2.
///
/// Elements of F[x]/(p(x)) are polynomials of degree < n, represented as
/// `Seq<F>` of length n (the coefficient vector [c_0, c_1, ..., c_{n-1}]).
///
/// The `coeffs()` method returns the lower n coefficients of p(x).
/// The leading coefficient (x^n) is implicitly 1 (monic).
pub trait MinimalPoly<F: Ring>: Sized {
    /// Degree of p(x). Must be at least 2.
    spec fn degree() -> nat;

    /// Lower coefficients [c_0, c_1, ..., c_{n-1}] of p(x) = x^n + c_{n-1}·x^{n-1} + ... + c_0.
    /// Length must equal degree().
    spec fn coeffs() -> Seq<F>;

    /// The degree is at least 2 (ensures nontrivial extension).
    proof fn axiom_degree_ge_2()
        ensures
            Self::degree() >= 2,
    ;

    /// The coefficient vector has exactly degree() entries.
    proof fn axiom_coeffs_len()
        ensures
            Self::coeffs().len() == Self::degree(),
    ;

    /// ═══════════════════════════════════════════════════════════════════
    ///  Multiplicative inverse (for Field axiom proofs)
    /// ═══════════════════════════════════════════════════════════════════
    ///
    /// Since p(x) is irreducible, every nonzero element in F[x]/(p(x)) has
    /// a multiplicative inverse. We add this as a trait axiom to avoid
    /// implementing polynomial extended GCD in the core library.
    ///
    /// The concrete inverse can be computed via extended Euclidean algorithm
    /// for specific instances (e.g., Rational, verus-rational).

    /// Inverse of a polynomial modulo p(x).
    /// Returns a polynomial of length degree() such that inverse(a) * a ≡ 1 (mod p).
    spec fn inverse_poly(a: Seq<F>) -> Seq<F>;

    /// The inverse is well-defined: length is correct.
    proof fn axiom_inverse_length(a: Seq<F>)
        requires
            a.len() == Self::degree(),
        ensures
            Self::inverse_poly(a).len() == Self::degree(),
    ;

    /// The inverse is actually an inverse: inverse(a) * a ≡ 1 (mod p).
    proof fn axiom_inverse_is_inverse(a: Seq<F>)
        requires
            a.len() == Self::degree(),
            // a is not zero polynomial
            exists|i: int| 0 <= i < Self::degree() as int && !(#[trigger] a[i]).eqv(F::zero()),
        ensures
            poly_eqv(
                ext_mul(Self::inverse_poly(a), a, Self::coeffs()),
                poly_one::<F>(Self::degree()),
            ),
    ;

    /// The inverse respects equivalence: if a ≡ b, then inverse(a) ≡ inverse(b).
    proof fn axiom_inverse_congruence(a: Seq<F>, b: Seq<F>)
        requires
            a.len() == Self::degree(),
            b.len() == Self::degree(),
            poly_eqv(a, b),
            // a (and thus b) is not zero
            exists|i: int| 0 <= i < Self::degree() as int && !(#[trigger] a[i]).eqv(F::zero()),
        ensures
            poly_eqv(Self::inverse_poly(a), Self::inverse_poly(b)),
    ;
}

} // verus!
