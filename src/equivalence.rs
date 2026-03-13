use crate::minimal_poly::MinimalPoly;
use crate::poly_arith::*;
use crate::spec::*;
use verus_algebra::traits::equivalence::Equivalence;
use verus_algebra::traits::ring::Ring;
use vstd::prelude::*;

verus! {

impl<F: Ring, P: MinimalPoly<F>> Equivalence for SpecFieldExt<F, P> {
    /// Component-wise equivalence using the base ring's eqv, up to P::degree().
    open spec fn eqv(self, other: Self) -> bool {
        fe_eqv::<F, P>(self, other)
    }

    proof fn axiom_eqv_reflexive(a: Self) {
        P::axiom_degree_ge_2();
        let n = P::degree();
        assert forall|i: int| 0 <= i < n as int
            implies coeff(a.coeffs, i).eqv(coeff(a.coeffs, i))
        by {
            F::axiom_eqv_reflexive(coeff(a.coeffs, i));
        }
    }

    proof fn axiom_eqv_symmetric(a: Self, b: Self) {
        P::axiom_degree_ge_2();
        let n = P::degree();
        // Need: fe_eqv(a, b) == fe_eqv(b, a), i.e. boolean equality of two foralls.
        // Establish pointwise boolean equality first.
        assert forall|i: int| 0 <= i < n as int
            implies coeff(a.coeffs, i).eqv(coeff(b.coeffs, i))
                == coeff(b.coeffs, i).eqv(coeff(a.coeffs, i))
        by {
            F::axiom_eqv_symmetric(coeff(a.coeffs, i), coeff(b.coeffs, i));
        }
        // Now lift: forall(f(i)) == forall(g(i)) when pointwise f(i) == g(i)
        assert(fe_eqv::<F, P>(a, b) == fe_eqv::<F, P>(b, a));
    }

    proof fn axiom_eqv_transitive(a: Self, b: Self, c: Self) {
        P::axiom_degree_ge_2();
        let n = P::degree();
        assert forall|i: int| 0 <= i < n as int
            implies coeff(a.coeffs, i).eqv(coeff(b.coeffs, i))
                && coeff(b.coeffs, i).eqv(coeff(c.coeffs, i))
            ==> coeff(a.coeffs, i).eqv(coeff(c.coeffs, i))
        by {
            if coeff(a.coeffs, i).eqv(coeff(b.coeffs, i))
                && coeff(b.coeffs, i).eqv(coeff(c.coeffs, i)) {
                F::axiom_eqv_transitive(
                    coeff(a.coeffs, i), coeff(b.coeffs, i), coeff(c.coeffs, i));
            }
        }
    }

    proof fn axiom_eq_implies_eqv(a: Self, b: Self) {
        P::axiom_degree_ge_2();
        let n = P::degree();
        // If a == b, then their coefficients are equal
        // Since F has axiom_eq_implies_eqv, equal coefficients are equivalent
        assert forall|i: int| 0 <= i < n as int
            implies coeff(a.coeffs, i).eqv(coeff(b.coeffs, i))
        by {
            if a == b {
                assert(a.coeffs[i] == b.coeffs[i]);
                F::axiom_eq_implies_eqv(a.coeffs[i], b.coeffs[i]);
            }
        }
    }
}

} // verus!
