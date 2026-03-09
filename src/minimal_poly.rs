use vstd::prelude::*;
use verus_algebra::traits::ring::Ring;

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
}

} // verus!
