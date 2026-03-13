use crate::minimal_poly::MinimalPoly;
use crate::poly_arith::*;
use crate::ring_lemmas;
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
        // This requires x to be nonzero. The Field trait precondition !x.eqv(Self::zero())
        // means exists i < n such that coeff(x.coeffs, i) != 0
        // Since x_norm[i] = coeff(x.coeffs, i) for i < n (because x_norm = normalize(x.coeffs, n)),
        // the same witness shows x_norm is nonzero
        assert forall|i: int| 0 <= i < n as int implies x_norm[i] == coeff(x.coeffs, i) by {}
        // From !x.eqv(Self::zero()) we have exists i < n where coeff(x.coeffs, i) != 0
        // The Field trait axiom_mul_recip_right has precondition !x.eqv(Self::zero())
        // which expands to exists|i| 0 <= i < n && !coeff(x.coeffs, i).eqv(F::zero())
        // Since x_norm[i] = coeff(x.coeffs, i) for i < n, these are equivalent.
        // We obtain the witness from the trait precondition.
        assert(exists|i: int| 0 <= i < n as int && !(#[trigger] x_norm[i]).eqv(F::zero())) by {
            // The trait precondition !x.eqv(Self::zero()) gives us exists|i| 0 <= i < n && !coeff(x.coeffs, i).eqv(F::zero())
            // Since x_norm[i] = coeff(x.coeffs, i) for i < n, the same witness works.
            // Unfold the trait precondition to get the witness
            let witness = choose|i: int| 0 <= i < n as int && !(#[trigger] coeff(x.coeffs, i)).eqv(F::zero());
            assert(0 <= witness < n as int);
            assert(!coeff(x.coeffs, witness).eqv(F::zero()));
            assert(x_norm[witness] == coeff(x.coeffs, witness));
            assert(!x_norm[witness].eqv(F::zero()));
            assert(0 <= witness < n as int && !x_norm[witness].eqv(F::zero()));
        };
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
        ring_lemmas::lemma_ext_mul_commutative::<F, P>(x_norm, inv);

        // Establish that normalize(fe_recip(x).coeffs, n) = inv
        // fe_recip(x).coeffs = inverse_poly(x_norm), which has length n
        // So normalize(fe_recip(x).coeffs, n) = inverse_poly(x_norm) = inv
        let recip_x = fe_recip::<F, P>(x);
        let recip_x_norm = normalize(recip_x.coeffs, n);

        // Since inv has length n, normalize(inv, n) =~= inv (both are sequences of length n with same elements)
        // Proof: normalize(s, n)[i] = coeff(s, i) = s[i] when s.len() == n and i < n
        assert forall|i: int| 0 <= i < n as int implies recip_x_norm[i] == inv[i] by {
            assert(recip_x_norm[i] == coeff(recip_x.coeffs, i));  // definition of normalize
            assert(coeff(recip_x.coeffs, i) == recip_x.coeffs[i]);  // since recip_x.coeffs.len() == n
            // recip_x.coeffs = P::inverse_poly(x_norm) = inv by definition
        }
        assert(recip_x_norm =~= inv);

        // Now verify the final result
        // fe_mul(x, fe_recip(x)).coeffs = ext_mul(x_norm, recip_x_norm, p)
        //                                    = ext_mul(x_norm, inv, p)
        //                                    ≡ poly_one(n) by the axiom and commutativity

        // The axiom gives us: poly_eqv(ext_mul(inv, x_norm, p), poly_one(n))
        // poly_eqv(a, b) means: a.len() == b.len() && forall i < a.len(), a[i] ≡ b[i]
        // So the axiom ensures: forall i < n, ext_mul(inv, x_norm, p)[i] ≡ poly_one(n)[i]

        // The commutativity lemma gives us:
        //   forall i < n, coeff(ext_mul(x_norm, inv, p), i) ≡ coeff(ext_mul(inv, x_norm, p), i)

        // To prove: forall i < n, coeff(fe_mul(x, recip(x)).coeffs, i) ≡ coeff(fe_one().coeffs, i)
        // Note: fe_mul(x, recip(x)).coeffs = ext_mul(x_norm, recip_x_norm, p)
        //       and recip_x_norm =~= inv (shown above)
        //       and coeff(fe_one().coeffs, i) = poly_one(n)[i] for i < n

        // First, establish the explicit connection from the axiom
        // poly_eqv(ext_mul(inv, x_norm, p), poly_one(n)) gives us coefficient-wise equivalence
        assert(ext_mul(inv, x_norm, P::coeffs()).len() == poly_one::<F>(n).len());
        assert(ext_mul(inv, x_norm, P::coeffs()).len() == n);
        assert(poly_one::<F>(n).len() == n);

        // Now prove the final result by connecting all pieces
        assert forall|i: int| 0 <= i < n as int
            implies coeff(fe_mul::<F, P>(x, fe_recip::<F, P>(x)).coeffs, i).eqv(
                coeff(fe_one::<F, P>().coeffs, i))
        by {
            // Step 1: fe_mul(x, recip(x)).coeffs = ext_mul(x_norm, recip_x_norm, p)
            //         and recip_x_norm =~= inv, so the coefficients match
            let lhs = coeff(fe_mul::<F, P>(x, fe_recip::<F, P>(x)).coeffs, i);
            let mid = coeff(ext_mul(x_norm, inv, P::coeffs()), i);
            assert(lhs == mid);  // Because recip_x_norm =~= inv

            // Step 2: By commutativity lemma (already invoked above)
            // coeff(ext_mul(x_norm, inv, p), i) ≡ coeff(ext_mul(inv, x_norm, p), i)
            let mid2 = coeff(ext_mul(inv, x_norm, P::coeffs()), i);
            // The commutativity lemma establishes this equivalence

            // Step 3: By the axiom (poly_eqv)
            // ext_mul(inv, x_norm, p)[i] ≡ poly_one(n)[i]
            let rhs = coeff(fe_one::<F, P>().coeffs, i);
            assert(rhs == poly_one::<F>(n)[i]);  // By definition of fe_one and coeff

            // Connect through transitivity
            // lhs = mid = coeff(ext_mul(x_norm, inv, p), i)
            // mid ≡ mid2 by commutativity
            // mid2 ≡ rhs by axiom (via poly_eqv)
            // Therefore lhs ≡ rhs

            // The commutativity lemma gives us mid ≡ mid2
            // The axiom (via poly_eqv) gives us mid2 ≡ rhs
            // So we need to chain these equivalences

            // Explicitly assert the equivalences we have
            assert(mid.eqv(mid2));  // From commutativity lemma
            assert(mid2.eqv(rhs));  // From axiom (poly_eqv unfolds to this)

            // Use transitivity
            F::axiom_eqv_transitive(mid, mid2, rhs);
            assert(mid.eqv(rhs));

            // Since lhs == mid (not just equivalent, but equal), we have lhs ≡ rhs
            assert(lhs.eqv(rhs));
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
        // Proof: a.eqv(b) means forall i < n, coeff(a.coeffs, i) ≡ coeff(b.coeffs, i)
        //        a_norm[i] = coeff(a.coeffs, i) and b_norm[i] = coeff(b.coeffs, i) for i < n
        //        So a_norm[i] ≡ b_norm[i] for all i < n
        //        This is exactly poly_eqv(a_norm, b_norm)
        assert(poly_eqv(a_norm, b_norm)) by {
            assert forall|i: int| 0 <= i < n as int implies a_norm[i].eqv(b_norm[i]) by {
                assert(a_norm[i] == coeff(a.coeffs, i));
                assert(b_norm[i] == coeff(b.coeffs, i));
            }
            assert(a_norm.len() == b_norm.len());
        };

        // Use the trait axiom for inverse congruence
        // First establish that a_norm is nonzero (from Field trait precondition !a.eqv(Self::zero()))
        // !a.eqv(Self::zero()) means exists i < n such that coeff(a.coeffs, i) != 0
        // Since a_norm[i] = coeff(a.coeffs, i) for i < n, the same witness shows a_norm is nonzero
        // The Field trait axiom_recip_congruence has precondition !a.eqv(Self::zero()), which gives us
        // exists|i| 0 <= i < n && !coeff(a.coeffs, i).eqv(F::zero()). Since a_norm[i] = coeff(a.coeffs, i),
        // the same witness works for the axiom precondition.
        assert(exists|i: int| 0 <= i < n as int && !(#[trigger] a_norm[i]).eqv(F::zero())) by {
            // The trait precondition !a.eqv(Self::zero()) gives us the witness
            let witness = choose|i: int| 0 <= i < n as int && !(#[trigger] coeff(a.coeffs, i)).eqv(F::zero());
            assert(0 <= witness < n as int);
            assert(!coeff(a.coeffs, witness).eqv(F::zero()));
            assert(a_norm[witness] == coeff(a.coeffs, witness));
            assert(!a_norm[witness].eqv(F::zero()));
        };

        // Establish length properties
        P::axiom_inverse_length(a_norm);
        P::axiom_inverse_length(b_norm);

        // Now use congruence axiom
        P::axiom_inverse_congruence(a_norm, b_norm);

        // Therefore fe_recip(a) ≡ fe_recip(b)
        // The axiom gives poly_eqv(inverse_poly(a_norm), inverse_poly(b_norm))
        // TODO: Connect poly_eqv to coefficient-wise equivalence via coeff()
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
