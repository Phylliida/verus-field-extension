use crate::assoc_lemmas;
use crate::minimal_poly::MinimalPoly;
use crate::poly_arith::*;
use crate::ring_lemmas;
use crate::spec::*;
use verus_algebra::traits::additive_commutative_monoid::AdditiveCommutativeMonoid;
use verus_algebra::traits::additive_group::AdditiveGroup;
use verus_algebra::traits::equivalence::Equivalence;
use verus_algebra::traits::ring::Ring;
use vstd::prelude::*;

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
    // Proved using Fubini's lemma and convolution associativity.

    proof fn axiom_mul_associative(a: Self, b: Self, c: Self) {
        P::axiom_degree_ge_2();
        P::axiom_coeffs_len();
        let n = P::degree();

        let a_n = normalize(a.coeffs, n);
        let b_n = normalize(b.coeffs, n);
        let c_n = normalize(c.coeffs, n);

        // Use the ext_mul_associative lemma from assoc_lemmas
        assoc_lemmas::lemma_ext_mul_associative::<F, P>(a_n, b_n, c_n);

        // The lemma proves: ext_mul(ext_mul(a,b), c) ≡ ext_mul(a, ext_mul(b,c))
        //
        // For fe_mul, we have:
        // fe_mul(x, y).coeffs = ext_mul(normalize(x.coeffs, n), normalize(y.coeffs, n), p)
        //
        // So:
        // fe_mul(fe_mul(a,b), c).coeffs = ext_mul(normalize(fe_mul(a,b).coeffs, n), c_n, p)
        // fe_mul(a,b).coeffs = ext_mul(a_n, b_n, p) which has length n
        // Since ext_mul returns length n, normalize doesn't change it
        // Therefore: fe_mul(fe_mul(a,b), c).coeffs = ext_mul(ext_mul(a_n, b_n, p), c_n, p)

        // Establish that fe_mul(a,b).coeffs has length n
        let ab = fe_mul::<F, P>(a, b);
        let bc = fe_mul::<F, P>(b, c);

        ring_lemmas::lemma_ext_mul_length::<F>(a_n, b_n, P::coeffs());
        ring_lemmas::lemma_ext_mul_length::<F>(b_n, c_n, P::coeffs());

        assert(ab.coeffs.len() == n);
        assert(bc.coeffs.len() == n);

        // Since the coefficients are equal (not just equivalent), we can assert the equivalence
        // The lemma proves coefficient-wise equivalence of the ext_mul results
        // Since fe_mul(...).coeffs = ext_mul(...), the equivalence transfers

        // When s.len() == n, normalize(s, n)[i] = coeff(s, i) = s[i] for i < n (equality, not just eqv)
        // So normalize(ab.coeffs, n) ≡ ab.coeffs pointwise, and similarly for bc
        assert forall|i: int| 0 <= i < n as int
            implies normalize(ab.coeffs, n)[i] == ab.coeffs[i]
        by { }
        assert forall|i: int| 0 <= i < n as int
            implies normalize(bc.coeffs, n)[i] == bc.coeffs[i]
        by { }

        // Use congruence: if normalize(ab.coeffs, n) ≡ ab.coeffs, then
        // ext_mul(normalize(ab.coeffs, n), c_n, p) ≡ ext_mul(ab.coeffs, c_n, p)
        // But we need the equivalence in terms of coeff, so prove pointwise eqv
        assert forall|i: int| 0 <= i < n as int
            implies normalize(ab.coeffs, n)[i].eqv(ab.coeffs[i])
        by { F::axiom_eqv_reflexive(ab.coeffs[i]); }
        assert forall|i: int| 0 <= i < n as int
            implies normalize(bc.coeffs, n)[i].eqv(bc.coeffs[i])
        by { F::axiom_eqv_reflexive(bc.coeffs[i]); }

        // Apply left congruence: ext_mul is congruent in its first argument
        // For LHS: ext_mul(normalize(ab.coeffs, n), c_n, p) ≡ ext_mul(ab.coeffs, c_n, p)
        ring_lemmas::lemma_ext_mul_congruence_left::<F, P>(normalize(ab.coeffs, n), ab.coeffs, c_n);
        // For RHS: ext_mul(normalize(bc.coeffs, n), a_n, p) ≡ ext_mul(bc.coeffs, a_n, p)
        ring_lemmas::lemma_ext_mul_congruence_left::<F, P>(normalize(bc.coeffs, n), bc.coeffs, a_n);

        // Now connect fe_mul results to ext_mul results
        // fe_mul(ab, c).coeffs = ext_mul(normalize(ab.coeffs, n), c_n, p)
        // fe_mul(a, bc).coeffs = ext_mul(a_n, normalize(bc.coeffs, n), p)
        let abc_lhs = fe_mul::<F, P>(ab, c);
        let abc_rhs = fe_mul::<F, P>(a, bc);

        // Use commutativity to align the ext_mul expressions
        ring_lemmas::lemma_ext_mul_commutative::<F, P>(normalize(bc.coeffs, n), a_n);
        ring_lemmas::lemma_ext_mul_commutative::<F, P>(bc.coeffs, a_n);

        // Now we have:
        // LHS: ext_mul(normalize(ab.coeffs, n), c_n, p) ≡ ext_mul(ab.coeffs, c_n, p) = ext_mul(ext_mul(a_n, b_n, p), c_n, p)
        // RHS: ext_mul(a_n, normalize(bc.coeffs, n), p) ≡ ext_mul(a_n, bc.coeffs, p) = ext_mul(a_n, ext_mul(b_n, c_n, p), p)

        // Key insight: fe_mul(x, y).coeffs = ext_mul(normalize(x.coeffs, n), normalize(y.coeffs, n), p)
        // When coeffs.len() == n, normalize(coeffs, n)[i] = coeffs[i] for all i < n
        // So normalize(coeffs, n) =~= coeffs as sequences

        // For abc_lhs = fe_mul(ab, c):
        // abc_lhs.coeffs = ext_mul(normalize(ab.coeffs, n), c_n, p)
        // Since ab.coeffs = ext_mul(a_n, b_n, p) has length n, normalize(ab.coeffs, n) =~= ab.coeffs
        // Therefore abc_lhs.coeffs =~= ext_mul(ab.coeffs, c_n, p) = ext_mul(ext_mul(a_n, b_n, p), c_n, p)

        // For abc_rhs = fe_mul(a, bc):
        // abc_rhs.coeffs = ext_mul(a_n, normalize(bc.coeffs, n), p)
        // Since bc.coeffs = ext_mul(b_n, c_n, p) has length n, normalize(bc.coeffs, n) =~= bc.coeffs
        // Therefore abc_rhs.coeffs =~= ext_mul(a_n, bc.coeffs, p) = ext_mul(a_n, ext_mul(b_n, c_n, p), p)

        // Show that normalize(ab.coeffs, n) =~= ab.coeffs since ab.coeffs.len() == n
        assert(normalize(ab.coeffs, n) =~= ab.coeffs) by {
            assert(ab.coeffs.len() == n);
            // Both have length n, and normalize(s, n)[i] = coeff(s, i) = s[i] when s.len() == n
        }

        // Show that normalize(bc.coeffs, n) =~= bc.coeffs since bc.coeffs.len() == n
        assert(normalize(bc.coeffs, n) =~= bc.coeffs) by {
            assert(bc.coeffs.len() == n);
        }

        // From the definitions:
        // abc_lhs.coeffs = ext_mul(normalize(ab.coeffs, n), c_n, p)
        // abc_rhs.coeffs = ext_mul(a_n, normalize(bc.coeffs, n), p)

        // By ext_mul_congruence_left and sequence equality:
        // ext_mul(normalize(ab.coeffs, n), c_n, p) ≡ ext_mul(ab.coeffs, c_n, p) pointwise
        // ext_mul(a_n, normalize(bc.coeffs, n), p) ≡ ext_mul(a_n, bc.coeffs, p) pointwise

        // Apply congruence lemmas
        ring_lemmas::lemma_ext_mul_congruence_left::<F, P>(normalize(ab.coeffs, n), ab.coeffs, c_n);
        ring_lemmas::lemma_ext_mul_congruence_right::<F, P>(a_n, normalize(bc.coeffs, n), bc.coeffs);

        // Now we need to connect ab.coeffs and bc.coeffs to their definitions
        // ab.coeffs = ext_mul(a_n, b_n, p) and bc.coeffs = ext_mul(b_n, c_n, p)

        assert forall|i: int| 0 <= i < n as int
            implies coeff(abc_lhs.coeffs, i).eqv(coeff(abc_rhs.coeffs, i))
        by {
            // lhs = coeff(abc_lhs.coeffs, i) = coeff(ext_mul(normalize(ab.coeffs, n), c_n, p), i)
            // rhs = coeff(abc_rhs.coeffs, i) = coeff(ext_mul(a_n, normalize(bc.coeffs, n), p), i)

            let lhs = coeff(abc_lhs.coeffs, i);
            let rhs = coeff(abc_rhs.coeffs, i);

            // From congruence: coeff(ext_mul(normalize(ab.coeffs, n), c_n, p), i) ≡ coeff(ext_mul(ab.coeffs, c_n, p), i)
            let lhs_mid = coeff(ext_mul(ab.coeffs, c_n, P::coeffs()), i);

            // From congruence: coeff(ext_mul(a_n, normalize(bc.coeffs, n), p), i) ≡ coeff(ext_mul(a_n, bc.coeffs, p), i)
            let rhs_mid = coeff(ext_mul(a_n, bc.coeffs, P::coeffs()), i);

            // By definition of ab and bc:
            // ab.coeffs = ext_mul(a_n, b_n, p), so coeff(ext_mul(ab.coeffs, c_n, p), i) = coeff(ext_mul(ext_mul(a_n, b_n, p), c_n, p), i)
            // bc.coeffs = ext_mul(b_n, c_n, p), so coeff(ext_mul(a_n, bc.coeffs, p), i) = coeff(ext_mul(a_n, ext_mul(b_n, c_n, p), p), i)

            let assoc_lhs = coeff(ext_mul(ext_mul(a_n, b_n, P::coeffs()), c_n, P::coeffs()), i);
            let assoc_rhs = coeff(ext_mul(a_n, ext_mul(b_n, c_n, P::coeffs()), P::coeffs()), i);

            // These follow from the lemma ensures
            assert(lhs.eqv(lhs_mid));
            assert(rhs.eqv(rhs_mid));

            // These follow from equality of ab.coeffs and bc.coeffs to the ext_mul expressions
            assert(lhs_mid.eqv(assoc_lhs));
            assert(rhs_mid.eqv(assoc_rhs));

            // From lemma_ext_mul_associative, we have assoc_lhs ≡ assoc_rhs
            assert(assoc_lhs.eqv(assoc_rhs));

            // Chain by transitivity
            F::axiom_eqv_transitive(lhs, lhs_mid, assoc_lhs);
            F::axiom_eqv_transitive(lhs, assoc_lhs, assoc_rhs);
            F::axiom_eqv_transitive(lhs, assoc_rhs, rhs_mid);
            F::axiom_eqv_transitive(lhs, rhs_mid, rhs);
        }
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
