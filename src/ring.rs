use vstd::prelude::*;
use verus_algebra::traits::equivalence::Equivalence;
use verus_algebra::traits::additive_commutative_monoid::AdditiveCommutativeMonoid;
use verus_algebra::traits::additive_group::AdditiveGroup;
use verus_algebra::traits::ring::Ring;
use crate::minimal_poly::MinimalPoly;
use crate::spec::*;
use crate::poly_arith::*;
use crate::ring_lemmas;

verus! {

impl<F: Ring, P: MinimalPoly<F>> Ring for SpecFieldExt<F, P> {
    open spec fn one() -> Self {
        fe_one::<F, P>()
    }

    open spec fn mul(self, other: Self) -> Self {
        fe_mul::<F, P>(self, other)
    }

    // ── Commutativity: a * b ≡ b * a ──────────────────────────────────

    proof fn axiom_mul_commutative(a: Self, b: Self) {
        P::axiom_degree_ge_2();
        P::axiom_coeffs_len();
        let n = P::degree();
        let a_n = normalize(a.coeffs, n);
        let b_n = normalize(b.coeffs, n);

        ring_lemmas::lemma_ext_mul_commutative::<F, P>(a_n, b_n);

        // fe_mul(a, b) uses normalize(a.coeffs, n) = a_n and normalize(b.coeffs, n) = b_n
        // fe_eqv compares coeff(result.coeffs, i) for i < n
        // Since ext_mul has length n, coeff(result, i) = result[i] for i < n
        assert forall|i: int| 0 <= i < n as int
            implies coeff(fe_mul::<F, P>(a, b).coeffs, i).eqv(
                coeff(fe_mul::<F, P>(b, a).coeffs, i))
        by {
            // fe_mul(a, b).coeffs = ext_mul(a_n, b_n, P::coeffs())
            // fe_mul(b, a).coeffs = ext_mul(b_n, a_n, P::coeffs())
            // Both have length n, so coeff just indexes
        }
    }

    // ── Associativity: (a * b) * c ≡ a * (b * c) ─────────────────────
    // Requires triple-sum rearrangement (Fubini) — deferred.

    proof fn axiom_mul_associative(a: Self, b: Self, c: Self) {
        assume(a.mul(b).mul(c).eqv(a.mul(b.mul(c))));
    }

    // ── Right identity: a * 1 ≡ a ─────────────────────────────────────

    proof fn axiom_mul_one_right(a: Self) {
        P::axiom_degree_ge_2();
        P::axiom_coeffs_len();
        let n = P::degree();
        let a_n = normalize(a.coeffs, n);
        let one_n = normalize(fe_one::<F, P>().coeffs, n);
        assert(one_n =~= poly_one::<F>(n));

        ring_lemmas::lemma_ext_mul_one_right::<F, P>(a_n);
        ring_lemmas::lemma_ext_mul_length::<F>(a_n, poly_one::<F>(n), P::coeffs());

        // The postcondition needs:
        //   forall|i| i < n ==> coeff(fe_mul(a, one).coeffs, i).eqv(coeff(a.coeffs, i))
        // fe_mul(a, one).coeffs = ext_mul(a_n, one_n, p) = ext_mul(a_n, poly_one(n), p)
        // lemma gives: coeff(ext_mul(a_n, poly_one(n), p), i) ≡ a_n[i] = coeff(a.coeffs, i)
        let result = ext_mul(a_n, poly_one::<F>(n), P::coeffs());
        assert(fe_mul::<F, P>(a, fe_one::<F, P>()).coeffs =~= result);
        assert(result.len() == n);
        assert forall|i: int| 0 <= i < n as int
            implies coeff(result, i).eqv(coeff(a.coeffs, i))
        by {
            // coeff(result, i) = result[i] since i < result.len()
            // From lemma: coeff(ext_mul(a_n, poly_one(n), p), i) ≡ a_n[i]
            // result == ext_mul(a_n, poly_one(n), p), a_n[i] == coeff(a.coeffs, i)
            assert(coeff(result, i) == result[i]);
            assert(a_n[i] == coeff(a.coeffs, i));
        }
    }

    // ── Zero annihilation: a * 0 ≡ 0 ──────────────────────────────────

    proof fn axiom_mul_zero_right(a: Self) {
        P::axiom_degree_ge_2();
        P::axiom_coeffs_len();
        let n = P::degree();
        let a_n = normalize(a.coeffs, n);

        // normalize(poly_zero(n), n) =~= poly_zero(n)
        let zero_n = normalize(fe_zero::<F, P>().coeffs, n);
        assert(zero_n =~= poly_zero::<F>(n));

        ring_lemmas::lemma_ext_mul_zero_right::<F, P>(a_n);
        ring_lemmas::lemma_ext_mul_length::<F>(a_n, poly_zero::<F>(n), P::coeffs());

        assert forall|i: int| 0 <= i < n as int
            implies coeff(fe_mul::<F, P>(a, fe_zero::<F, P>()).coeffs, i).eqv(
                coeff(fe_zero::<F, P>().coeffs, i))
        by {
            F::axiom_eqv_reflexive(F::zero());
        }
    }

    // ── Distributivity: a * (b + c) ≡ a*b + a*c ───────────────────────

    proof fn axiom_mul_distributes_left(a: Self, b: Self, c: Self) {
        P::axiom_degree_ge_2();
        P::axiom_coeffs_len();
        let n = P::degree();
        let a_n = normalize(a.coeffs, n);
        let b_n = normalize(b.coeffs, n);
        let c_n = normalize(c.coeffs, n);

        // fe_mul(a, fe_add(b, c)):
        //   normalize(fe_add(b,c).coeffs, n) = normalize(Seq::new(n, |i| coeff(b,i)+coeff(c,i)), n)
        //   = Seq::new(n, |i| coeff(Seq::new(n, |j| coeff(b,j)+coeff(c,j)), i))
        //   For i < n: the inner Seq has length n, so coeff = b_n[i]+c_n[i] = poly_add(b_n, c_n)[i]
        //   So normalize(fe_add.coeffs, n) = poly_add(b_n, c_n)

        // Show normalize of fe_add result equals poly_add of normalizations
        let bc_add = fe_add::<F, P>(b, c);
        let bc_norm = normalize(bc_add.coeffs, n);
        let bc_direct = poly_add(b_n, c_n);

        // These are equal (not just eqv) by Seq extensionality
        assert(bc_norm =~= bc_direct);

        ring_lemmas::lemma_ext_mul_distributes_left::<F, P>(a_n, b_n, c_n);
        ring_lemmas::lemma_ext_mul_length::<F>(a_n, bc_direct, P::coeffs());
        ring_lemmas::lemma_ext_mul_length::<F>(a_n, b_n, P::coeffs());
        ring_lemmas::lemma_ext_mul_length::<F>(a_n, c_n, P::coeffs());

        // LHS: fe_mul(a, fe_add(b, c)).coeffs = ext_mul(a_n, bc_norm, p) = ext_mul(a_n, bc_direct, p)
        // RHS: fe_add(fe_mul(a, b), fe_mul(a, c)).coeffs[i] =
        //   coeff(fe_mul(a,b).coeffs, i) + coeff(fe_mul(a,c).coeffs, i)
        //   = ext_mul(a_n, b_n, p)[i] + ext_mul(a_n, c_n, p)[i]

        assert forall|i: int| 0 <= i < n as int
            implies coeff(fe_mul::<F, P>(a, bc_add).coeffs, i).eqv(
                coeff(fe_add::<F, P>(fe_mul::<F, P>(a, b), fe_mul::<F, P>(a, c)).coeffs, i))
        by {
            // LHS coeff = ext_mul(a_n, bc_direct, p)[i]
            // This ≡ ext_mul(a_n, b_n, p)[i] + ext_mul(a_n, c_n, p)[i] by lemma
            // RHS coeff = coeff(mul_ab, i) + coeff(mul_ac, i)
            //   mul_ab.coeffs has length n, mul_ac.coeffs has length n
            //   so these are just the ext_mul results indexed at i
        }
    }

    // ── Non-degeneracy: 1 ≢ 0 ──────────────────────────────────────────

    proof fn axiom_one_ne_zero() {
        P::axiom_degree_ge_2();
        ring_lemmas::lemma_ext_one_ne_zero::<F, P>();
    }

    // ── Left congruence: a ≡ b implies a*c ≡ b*c ──────────────────────

    proof fn axiom_mul_congruence_left(a: Self, b: Self, c: Self) {
        P::axiom_degree_ge_2();
        P::axiom_coeffs_len();
        let n = P::degree();
        let a_n = normalize(a.coeffs, n);
        let b_n = normalize(b.coeffs, n);
        let c_n = normalize(c.coeffs, n);

        // a.eqv(b) means coeff(a.coeffs, i).eqv(coeff(b.coeffs, i)) for i < n
        // which means a_n[i].eqv(b_n[i]) for i < n
        assert forall|i: int| 0 <= i < n as int implies (#[trigger] a_n[i]).eqv(b_n[i])
        by { }

        ring_lemmas::lemma_ext_mul_congruence_left::<F, P>(a_n, b_n, c_n);

        assert forall|i: int| 0 <= i < n as int
            implies coeff(fe_mul::<F, P>(a, c).coeffs, i).eqv(
                coeff(fe_mul::<F, P>(b, c).coeffs, i))
        by { }
    }
}

} // verus!
