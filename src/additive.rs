use crate::minimal_poly::MinimalPoly;
use crate::poly_arith::*;
use crate::spec::*;
use verus_algebra::traits::additive_commutative_monoid::AdditiveCommutativeMonoid;
use verus_algebra::traits::additive_group::AdditiveGroup;
use verus_algebra::traits::equivalence::Equivalence;
use verus_algebra::traits::ring::Ring;
use vstd::prelude::*;

verus! {

// ═══════════════════════════════════════════════════════════════════
//  AdditiveCommutativeMonoid for SpecFieldExt<F, P>
// ═══════════════════════════════════════════════════════════════════

impl<F: Ring, P: MinimalPoly<F>> AdditiveCommutativeMonoid for SpecFieldExt<F, P> {
    open spec fn zero() -> Self {
        fe_zero::<F, P>()
    }

    open spec fn add(self, other: Self) -> Self {
        fe_add::<F, P>(self, other)
    }

    proof fn axiom_add_commutative(a: Self, b: Self) {
        P::axiom_degree_ge_2();
        let n = P::degree();
        // a.add(b) has coeffs[i] = coeff(a, i) + coeff(b, i)
        // b.add(a) has coeffs[i] = coeff(b, i) + coeff(a, i)
        // eqv compares coeff(result, i) = result.coeffs[i] since both have length n
        assert forall|i: int| 0 <= i < n as int
            implies coeff(a.coeffs, i).add(coeff(b.coeffs, i)).eqv(
                coeff(b.coeffs, i).add(coeff(a.coeffs, i)))
        by {
            F::axiom_add_commutative(coeff(a.coeffs, i), coeff(b.coeffs, i));
        }
    }

    proof fn axiom_add_associative(a: Self, b: Self, c: Self) {
        P::axiom_degree_ge_2();
        let n = P::degree();
        // (a + b) + c: first compute a+b (length n), then add c
        // coeff((a+b).coeffs, i) = (a+b).coeffs[i] = coeff(a,i) + coeff(b,i)
        // ((a+b)+c).coeffs[i] = coeff((a+b).coeffs, i) + coeff(c,i)
        //                     = (coeff(a,i) + coeff(b,i)) + coeff(c,i)
        //
        // a + (b+c): similarly = coeff(a,i) + (coeff(b,i) + coeff(c,i))
        assert forall|i: int| 0 <= i < n as int
            implies coeff(a.coeffs, i).add(coeff(b.coeffs, i)).add(coeff(c.coeffs, i)).eqv(
                coeff(a.coeffs, i).add(coeff(b.coeffs, i).add(coeff(c.coeffs, i))))
        by {
            F::axiom_add_associative(
                coeff(a.coeffs, i), coeff(b.coeffs, i), coeff(c.coeffs, i));
        }
    }

    proof fn axiom_add_zero_right(a: Self) {
        P::axiom_degree_ge_2();
        let n = P::degree();
        // a + zero: coeffs[i] = coeff(a,i) + coeff(poly_zero(n), i)
        //                      = coeff(a,i) + F::zero()
        // eqv with a: coeff(a,i)
        assert forall|i: int| 0 <= i < n as int
            implies coeff(a.coeffs, i).add(F::zero()).eqv(coeff(a.coeffs, i))
        by {
            F::axiom_add_zero_right(coeff(a.coeffs, i));
        }
    }

    proof fn axiom_add_congruence_left(a: Self, b: Self, c: Self) {
        P::axiom_degree_ge_2();
        let n = P::degree();
        assert forall|i: int| 0 <= i < n as int
            implies coeff(a.coeffs, i).add(coeff(c.coeffs, i)).eqv(
                coeff(b.coeffs, i).add(coeff(c.coeffs, i)))
        by {
            // From a.eqv(b): coeff(a,i).eqv(coeff(b,i))
            F::axiom_add_congruence_left(
                coeff(a.coeffs, i), coeff(b.coeffs, i), coeff(c.coeffs, i));
        }
    }
}

// ═══════════════════════════════════════════════════════════════════
//  AdditiveGroup for SpecFieldExt<F, P>
// ═══════════════════════════════════════════════════════════════════

impl<F: Ring, P: MinimalPoly<F>> AdditiveGroup for SpecFieldExt<F, P> {
    open spec fn neg(self) -> Self {
        fe_neg::<F, P>(self)
    }

    open spec fn sub(self, other: Self) -> Self {
        fe_sub::<F, P>(self, other)
    }

    proof fn axiom_add_inverse_right(a: Self) {
        P::axiom_degree_ge_2();
        let n = P::degree();
        // a + neg(a): coeffs[i] = coeff(a,i) + coeff(neg(a).coeffs, i)
        //   neg(a).coeffs = Seq::new(n, |j| coeff(a,j).neg()), length n
        //   so coeff(neg(a).coeffs, i) = coeff(a,i).neg() for i < n
        // Result: coeff(a,i) + coeff(a,i).neg() ≡ 0
        assert forall|i: int| 0 <= i < n as int
            implies coeff(a.coeffs, i).add(coeff(a.coeffs, i).neg()).eqv(F::zero())
        by {
            F::axiom_add_inverse_right(coeff(a.coeffs, i));
        }
    }

    proof fn axiom_sub_is_add_neg(a: Self, b: Self) {
        P::axiom_degree_ge_2();
        let n = P::degree();
        // sub(a,b).coeffs[i] = coeff(a,i).sub(coeff(b,i))
        // add(a, neg(b)).coeffs[i] = coeff(a,i).add(coeff(neg(b).coeffs, i))
        //   = coeff(a,i).add(coeff(b,i).neg())
        assert forall|i: int| 0 <= i < n as int
            implies coeff(a.coeffs, i).sub(coeff(b.coeffs, i)).eqv(
                coeff(a.coeffs, i).add(coeff(b.coeffs, i).neg()))
        by {
            F::axiom_sub_is_add_neg(coeff(a.coeffs, i), coeff(b.coeffs, i));
        }
    }

    proof fn axiom_neg_congruence(a: Self, b: Self) {
        P::axiom_degree_ge_2();
        let n = P::degree();
        assert forall|i: int| 0 <= i < n as int
            implies coeff(a.coeffs, i).neg().eqv(coeff(b.coeffs, i).neg())
        by {
            // From a.eqv(b): coeff(a,i).eqv(coeff(b,i))
            F::axiom_neg_congruence(coeff(a.coeffs, i), coeff(b.coeffs, i));
        }
    }
}

} // verus!
