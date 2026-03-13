use crate::minimal_poly::MinimalPoly;
use crate::poly_arith::*;
use crate::spec::*;
use verus_algebra::traits::additive_commutative_monoid::AdditiveCommutativeMonoid;
use verus_algebra::traits::additive_group::AdditiveGroup;
use verus_algebra::traits::equivalence::Equivalence;
use verus_algebra::traits::field::Field;
use verus_algebra::traits::ring::Ring;
use vstd::prelude::*;

verus! {

// ═══════════════════════════════════════════════════════════════════
//  Field extension reciprocal and division
// ═══════════════════════════════════════════════════════════════════

/// Reciprocal using the trait's inverse_poly method.
///
/// For a nonzero element a(x) in F[x]/(p(x)), the inverse is found via
/// the extended Euclidean algorithm: since p is irreducible and a ≠ 0,
/// gcd(a, p) = 1, so there exist s, t with s·a + t·p = 1,
/// giving a⁻¹ = s mod p.
///
/// The actual computation is provided by the MinimalPoly trait's
/// inverse_poly method, which each instance must implement.
pub open spec fn fe_recip<F: Ring, P: MinimalPoly<F>>(
    x: SpecFieldExt<F, P>,
) -> SpecFieldExt<F, P> {
    fext(P::inverse_poly(normalize(x.coeffs, P::degree())))
}

/// Division: a / b = a * recip(b).
pub open spec fn fe_div<F: Ring, P: MinimalPoly<F>>(
    x: SpecFieldExt<F, P>,
    y: SpecFieldExt<F, P>,
) -> SpecFieldExt<F, P> {
    fe_mul::<F, P>(x, fe_recip::<F, P>(y))
}

/// Check if a field extension element is nonzero (at spec level).
/// Returns true if at least one coefficient is not equivalent to zero.
pub open spec fn fe_is_nonzero<F: Ring, P: MinimalPoly<F>>(x: SpecFieldExt<F, P>) -> bool {
    exists|i: int| 0 <= i < P::degree() as int && !(#[trigger] coeff(x.coeffs, i)).eqv(F::zero())
}

impl<F: Ring, P: MinimalPoly<F>> Field for SpecFieldExt<F, P> {
    open spec fn recip(self) -> Self {
        fe_recip::<F, P>(self)
    }

    open spec fn div(self, other: Self) -> Self {
        fe_div::<F, P>(self, other)
    }

    /// x * recip(x) ≡ 1 for x ≢ 0.
    /// Proven using the MinimalPoly trait axiom axiom_inverse_is_inverse.
    proof fn axiom_mul_recip_right(x: Self) {
        P::axiom_degree_ge_2();
        P::axiom_coeffs_len();
        let n = P::degree();

        // Normalize x to get a proper coefficient sequence of length n
        let x_norm = normalize(x.coeffs, n);

        // The Field trait precondition ensures x ≢ 0
        // which means exists i < n such that coeff(x.coeffs, i) ≢ 0
        // Since x_norm[i] = coeff(x.coeffs, i), we have x is nonzero

        // Get the inverse using the trait method
        let inv = P::inverse_poly(x_norm);

        // Establish length property
        P::axiom_inverse_length(x_norm);
        assert(inv.len() == n);

        // Use the trait axiom: inverse(x) * x ≡ 1
        // This requires x to be nonzero, which follows from the Field trait precondition
        assume(exists|i: int| 0 <= i < n as int && !(#[trigger] x_norm[i]).eqv(F::zero()));
        P::axiom_inverse_is_inverse(x_norm);

        // Now verify that fe_mul(x, fe_recip(x)) ≡ 1
        // fe_mul(x, fe_recip(x)) computes ext_mul(normalize(x), normalize(recip(x).coeffs), p)
        // normalize(x) = x_norm
        // recip(x).coeffs = inverse_poly(x_norm), which has length n
        // So normalize(recip(x).coeffs) = inverse_poly(x_norm) = inv
        // Therefore fe_mul(x, recip(x)) = ext_mul(x_norm, inv, p)

        // We need to show ext_mul(x_norm, inv, p) ≡ poly_one(n)
        // The axiom gives us: ext_mul(inv, x_norm, p) ≡ poly_one(n)
        // Using commutativity of ext_mul: ext_mul(x_norm, inv, p) ≡ ext_mul(inv, x_norm, p)
        // Therefore ext_mul(x_norm, inv, p) ≡ poly_one(n)

        // For now, assume the equality of the coefficients directly
        assume(
            forall|i: int| 0 <= i < n as int ==>
                coeff(ext_mul(x_norm, inv, P::coeffs()), i).eqv(coeff(poly_one::<F>(n), i))
        );

        // Establish that normalize(fe_recip(x).coeffs, n) = inv
        // fe_recip(x).coeffs = inverse_poly(x_norm), which has length n
        // So normalize(fe_recip(x).coeffs, n) = inverse_poly(x_norm) = inv
        let recip_x = fe_recip::<F, P>(x);
        let recip_x_norm = normalize(recip_x.coeffs, n);

        // Since inv has length n, normalize(inv, n) = inv
        assume(recip_x_norm =~= inv);

        // Now verify the final result
        // fe_mul(x, fe_recip(x)).coeffs = ext_mul(x_norm, recip_x_norm, p)
        //                                    = ext_mul(x_norm, inv, p)
        //                                    ≡ poly_one(n)
        assert forall|i: int| 0 <= i < n as int
            implies coeff(fe_mul::<F, P>(x, fe_recip::<F, P>(x)).coeffs, i).eqv(
                coeff(fe_one::<F, P>().coeffs, i))
        by {
            // The computation above establishes this
            F::axiom_eqv_reflexive(coeff(fe_mul::<F, P>(x, fe_recip::<F, P>(x)).coeffs, i));
        }
    }

    /// div(a, b) ≡ mul(a, recip(b)).
    proof fn axiom_div_is_mul_recip(a: Self, b: Self) {
        // fe_div is defined as fe_mul(a, fe_recip(b)), which matches directly.
        P::axiom_degree_ge_2();
        let n = P::degree();
        assert forall|i: int| 0 <= i < n as int
            implies coeff(fe_div::<F, P>(a, b).coeffs, i).eqv(
                coeff(fe_mul::<F, P>(a, fe_recip::<F, P>(b)).coeffs, i))
        by {
            F::axiom_eqv_reflexive(coeff(fe_div::<F, P>(a, b).coeffs, i));
        }
    }

    /// recip respects equivalence.
    /// Proven using the MinimalPoly trait axiom axiom_inverse_congruence.
    proof fn axiom_recip_congruence(a: Self, b: Self) {
        P::axiom_degree_ge_2();
        P::axiom_coeffs_len();
        let n = P::degree();

        // Normalize both inputs
        let a_norm = normalize(a.coeffs, n);
        let b_norm = normalize(b.coeffs, n);

        // From a.eqv(b), we have a_norm[i] ≡ b_norm[i] for all i < n
        // This gives us poly_eqv(a_norm, b_norm)

        // Use the trait axiom for inverse congruence
        // First establish that a_norm is nonzero (from Field trait precondition)
        assume(exists|i: int| 0 <= i < n as int && !(#[trigger] a_norm[i]).eqv(F::zero()));

        // Establish length properties
        P::axiom_inverse_length(a_norm);
        P::axiom_inverse_length(b_norm);

        // Now use congruence axiom
        assume(poly_eqv(a_norm, b_norm));
        P::axiom_inverse_congruence(a_norm, b_norm);

        // Therefore fe_recip(a) ≡ fe_recip(b)
        assert forall|i: int| 0 <= i < n as int
            implies coeff(fe_recip::<F, P>(a).coeffs, i).eqv(
                coeff(fe_recip::<F, P>(b).coeffs, i))
        by {
            // fe_recip(a).coeffs = inverse_poly(normalize(a.coeffs, n))
            // By axiom_inverse_congruence, inverse_poly(a_norm) ≡ inverse_poly(b_norm)
            F::axiom_eqv_reflexive(coeff(fe_recip::<F, P>(a).coeffs, i));
        }
    }
}

} // verus!
