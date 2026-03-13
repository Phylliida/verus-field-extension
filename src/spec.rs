use crate::minimal_poly::MinimalPoly;
use crate::poly_arith::*;
use verus_algebra::traits::additive_commutative_monoid::AdditiveCommutativeMonoid;
use verus_algebra::traits::additive_group::AdditiveGroup;
use verus_algebra::traits::equivalence::Equivalence;
use verus_algebra::traits::ring::Ring;
use vstd::prelude::*;

verus! {

// ═══════════════════════════════════════════════════════════════════
//  Spec type: elements of the field extension F[x]/(p(x))
// ═══════════════════════════════════════════════════════════════════

/// Spec-level element of the field extension F[x]/(p(x)).
///
/// Represents a polynomial of degree < deg(p) via its coefficient vector.
/// The minimal polynomial is fixed at the type level via P.
///
/// All operations normalize via `coeff` (zero-padded safe access) so that
/// trait axioms hold for arbitrary values, not just well-formed ones.
pub ghost struct SpecFieldExt<F, P> {
    pub coeffs: Seq<F>,
    pub _phantom: core::marker::PhantomData<P>,
}

/// Constructor that avoids writing PhantomData everywhere.
pub open spec fn fext<F, P>(coeffs: Seq<F>) -> SpecFieldExt<F, P> {
    SpecFieldExt { coeffs, _phantom: core::marker::PhantomData }
}

// ═══════════════════════════════════════════════════════════════════
//  Open spec functions for field extension arithmetic
// ═══════════════════════════════════════════════════════════════════
//
// All operations use `coeff(x.coeffs, i)` for safe access and always
// produce outputs of length P::degree(). This ensures trait axioms
// hold for all values, including malformed ones with wrong-length coeffs.

/// Well-formedness: coefficient vector has the right length.
pub open spec fn fe_wf<F: Ring, P: MinimalPoly<F>>(x: SpecFieldExt<F, P>) -> bool {
    x.coeffs.len() == P::degree()
}

/// Zero: the zero polynomial [0, 0, ..., 0].
pub open spec fn fe_zero<F: Ring, P: MinimalPoly<F>>() -> SpecFieldExt<F, P> {
    fext(poly_zero::<F>(P::degree()))
}

/// One: the constant polynomial [1, 0, ..., 0].
pub open spec fn fe_one<F: Ring, P: MinimalPoly<F>>() -> SpecFieldExt<F, P> {
    fext(poly_one::<F>(P::degree()))
}

/// Addition: component-wise via coeff, always length n.
pub open spec fn fe_add<F: Ring, P: MinimalPoly<F>>(
    x: SpecFieldExt<F, P>,
    y: SpecFieldExt<F, P>,
) -> SpecFieldExt<F, P> {
    let n = P::degree();
    fext(Seq::new(n, |i: int| coeff(x.coeffs, i).add(coeff(y.coeffs, i))))
}

/// Negation: component-wise via coeff, always length n.
pub open spec fn fe_neg<F: Ring, P: MinimalPoly<F>>(
    x: SpecFieldExt<F, P>,
) -> SpecFieldExt<F, P> {
    let n = P::degree();
    fext(Seq::new(n, |i: int| coeff(x.coeffs, i).neg()))
}

/// Subtraction: component-wise via coeff, always length n.
pub open spec fn fe_sub<F: Ring, P: MinimalPoly<F>>(
    x: SpecFieldExt<F, P>,
    y: SpecFieldExt<F, P>,
) -> SpecFieldExt<F, P> {
    let n = P::degree();
    fext(Seq::new(n, |i: int| coeff(x.coeffs, i).sub(coeff(y.coeffs, i))))
}

/// Normalize a coefficient vector to length n using coeff (zero-padded).
pub open spec fn normalize<F: Ring>(coeffs: Seq<F>, n: nat) -> Seq<F> {
    Seq::new(n, |i: int| coeff(coeffs, i))
}

/// Multiplication: normalize inputs, convolve, then reduce mod p(x).
pub open spec fn fe_mul<F: Ring, P: MinimalPoly<F>>(
    x: SpecFieldExt<F, P>,
    y: SpecFieldExt<F, P>,
) -> SpecFieldExt<F, P> {
    let n = P::degree();
    let a = normalize(x.coeffs, n);
    let b = normalize(y.coeffs, n);
    fext(ext_mul(a, b, P::coeffs()))
}

/// Component-wise equivalence, compared up to P::degree() via coeff.
pub open spec fn fe_eqv<F: Ring, P: MinimalPoly<F>>(
    x: SpecFieldExt<F, P>,
    y: SpecFieldExt<F, P>,
) -> bool {
    let n = P::degree();
    forall|i: int| 0 <= i < n as int ==> coeff(x.coeffs, i).eqv(coeff(y.coeffs, i))
}

} // verus!
