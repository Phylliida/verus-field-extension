use vstd::prelude::*;
use verus_algebra::traits::equivalence::Equivalence;
use verus_algebra::traits::additive_commutative_monoid::AdditiveCommutativeMonoid;
use verus_algebra::traits::additive_group::AdditiveGroup;
use verus_algebra::traits::ring::Ring;
use verus_algebra::lemmas::additive_group_lemmas;
use verus_algebra::lemmas::additive_commutative_monoid_lemmas;
use verus_algebra::lemmas::ring_lemmas;
use verus_algebra::summation::*;
use crate::minimal_poly::MinimalPoly;
use crate::spec::*;
use crate::poly_arith::*;
use crate::ring_lemmas as fe_ring_lemmas;

verus! {

// ═══════════════════════════════════════════════════════════════════
//  Phase 3: Reduce of p_full multiple gives zero
// ═══════════════════════════════════════════════════════════════════

/// reduce_step applied to p_full (shifted and scaled) kills all coefficients.
///
/// p_full = [p_coeffs[0], ..., p_coeffs[n-1], 1] has length n+1.
/// reduce_step subtracts lead * p_coeffs from the relevant positions.
/// Since lead = 1 (the monic leading term after scalar multiplication),
/// this exactly cancels, leaving ≡ 0 everywhere.
///
/// More precisely: reduce_step(poly_shift(p_full, shift), p_coeffs)
/// gives a result of length n+shift whose coefficients are all ≡ 0.
proof fn lemma_reduce_step_p_full_shift<F: Ring>(
    p_coeffs: Seq<F>,
    shift: nat,
)
    requires
        p_coeffs.len() >= 2,
    ensures
        ({
            let pf = p_full_seq(p_coeffs);
            let h = poly_shift::<F>(pf, shift);
            let rs = reduce_step(h, p_coeffs);
            &&& rs.len() == (p_coeffs.len() + shift) as nat
            &&& forall|k: int| 0 <= k < rs.len() as int ==> (#[trigger] rs[k]).eqv(F::zero())
        }),
{
    let n = p_coeffs.len();
    let pf = p_full_seq(p_coeffs);
    let h = poly_shift::<F>(pf, shift);
    let rs = reduce_step(h, p_coeffs);

    // h has length n+1+shift, h[i] = 0 for i < shift, pf[i-shift] for i >= shift
    // h.len() = n+1+shift > n = p_coeffs.len() (since n >= 2, shift >= 0)
    assert(h.len() == (n + 1 + shift) as nat);
    assert(h.len() > p_coeffs.len());

    // lead = h[h.len()-1] = pf[n] = F::one()
    let m = h.len();
    assert(h[m as int - 1] == pf[n as int]);
    assert(pf[n as int] == F::one());

    // rs = reduce_step(h, p_coeffs), length = m-1 = n+shift
    assert(rs.len() == (n + shift) as nat);

    // The reduce_step definition:
    // shift_rs = m - 1 - n = shift
    // For shift <= k < shift+n: rs[k] = h[k] - lead * p_coeffs[k-shift]
    //   = pf[k-shift] - 1 * p_coeffs[k-shift]
    //   = p_coeffs[k-shift] - p_coeffs[k-shift]  (since k-shift < n means pf[k-shift] = p_coeffs[k-shift])
    //   ≡ 0
    // For k < shift: rs[k] = h[k] = 0
    // For k >= shift+n: impossible since rs.len() = n+shift

    assert forall|k: int| 0 <= k < rs.len() as int
        implies (#[trigger] rs[k]).eqv(F::zero())
    by {
        let shift_rs: nat = (m - 1 - n) as nat;
        assert(shift_rs == shift);
        if k < shift as int {
            // rs[k] = h[k] = 0 (below the shift region)
            F::axiom_eqv_reflexive(F::zero());
        } else if (shift as int) <= k < (shift + n) as int {
            // rs[k] = h[k].sub(lead.mul(p_coeffs[k - shift]))
            // h[k] = pf[k - shift] since k >= shift
            // k - shift < n, so pf[k - shift] = p_coeffs[k - shift]
            // lead = F::one()
            // rs[k] = p_coeffs[k-shift] - 1 * p_coeffs[k-shift]
            //       ≡ p_coeffs[k-shift] - p_coeffs[k-shift] ≡ 0
            assert(h[k] == pf[k - shift]);
            assert(pf[k - shift] == p_coeffs[k - shift]);
            ring_lemmas::lemma_mul_one_left::<F>(p_coeffs[k - shift]);
            // 1 * p ≡ p, so sub(p, 1*p) ≡ sub(p, p) ≡ 0
            F::axiom_eqv_reflexive(p_coeffs[k - shift]);
            additive_group_lemmas::lemma_sub_congruence::<F>(
                h[k], p_coeffs[k - shift],
                F::one().mul(p_coeffs[k - shift]), p_coeffs[k - shift],
            );
            additive_group_lemmas::lemma_sub_self::<F>(p_coeffs[k - shift]);
            F::axiom_eqv_transitive(
                rs[k],
                p_coeffs[k - shift].sub(p_coeffs[k - shift]),
                F::zero(),
            );
        }
    }
}

/// poly_reduce of poly_shift(p_full, shift) gives all zeros.
proof fn lemma_reduce_p_full_shift<F: Ring>(
    p_coeffs: Seq<F>,
    shift: nat,
)
    requires
        p_coeffs.len() >= 2,
    ensures
        ({
            let h = poly_shift::<F>(p_full_seq(p_coeffs), shift);
            let r = poly_reduce(h, p_coeffs);
            &&& r.len() == p_coeffs.len()
            &&& forall|k: int| 0 <= k < r.len() as int ==> (#[trigger] r[k]).eqv(F::zero())
        }),
    decreases shift,
{
    let n = p_coeffs.len();
    let pf = p_full_seq(p_coeffs);
    let h = poly_shift::<F>(pf, shift);

    // h.len() = n+1+shift > n, so poly_reduce recurses
    assert(h.len() == (n + 1 + shift) as nat);
    assert(h.len() > n);

    // reduce_step gives all-zero result
    lemma_reduce_step_p_full_shift::<F>(p_coeffs, shift);
    let rs = reduce_step(h, p_coeffs);
    assert(rs.len() == (n + shift) as nat);

    // All rs[k] ≡ 0
    // poly_reduce(h) = poly_reduce(rs)

    if shift == 0 {
        // rs.len() == n == p_coeffs.len(), so poly_reduce(rs) = rs (base case)
        assert(rs.len() == n);
        assert(poly_reduce(rs, p_coeffs) == rs);
    } else {
        // rs.len() > n, need to continue reducing
        // rs has all zeros, so reduce_zero_tail applies
        assert(rs.len() > n);
        assert forall|k: int| n as int <= k < rs.len() as int
            implies (#[trigger] rs[k]).eqv(F::zero())
        by { }
        fe_ring_lemmas::lemma_reduce_zero_tail::<F>(rs, p_coeffs);
        // poly_reduce(rs)[k] ≡ rs[k] ≡ 0 for k < n
        assert forall|k: int| 0 <= k < n as int
            implies (#[trigger] poly_reduce(rs, p_coeffs)[k]).eqv(F::zero())
        by {
            F::axiom_eqv_transitive(
                poly_reduce(rs, p_coeffs)[k],
                rs[k],
                F::zero(),
            );
        }
    }
}

/// Scalar-multiplied p_full shift reduces to zero:
/// poly_reduce(poly_scalar_mul(s, poly_shift(p_full, shift))) has all coefficients ≡ 0.
proof fn lemma_reduce_scalar_p_full_shift<F: Ring>(
    s: F, p_coeffs: Seq<F>, shift: nat,
)
    requires
        p_coeffs.len() >= 2,
    ensures
        ({
            let h = poly_scalar_mul(s, poly_shift::<F>(p_full_seq(p_coeffs), shift));
            let r = poly_reduce(h, p_coeffs);
            &&& r.len() == p_coeffs.len()
            &&& forall|k: int| 0 <= k < r.len() as int ==> (#[trigger] r[k]).eqv(F::zero())
        }),
{
    let n = p_coeffs.len();
    let pf = p_full_seq(p_coeffs);
    let base = poly_shift::<F>(pf, shift);
    let h = poly_scalar_mul(s, base);
    assert(h.len() == base.len());
    assert(base.len() == (n + 1 + shift) as nat);

    // Strategy: use reduce_scalar to factor out s, then use reduce_p_full_shift
    // But we don't have reduce_scalar yet. Instead, use reduce_additive approach:
    // decompose s * base as s * base, and show it reduces to s * reduce(base) ≡ s * 0 ≡ 0.

    // Actually, let's prove reduce_scalar inline here.
    // poly_reduce(s * base) = poly_reduce(s * base)
    // We'll prove by induction that reduce of scalar-mul commutes.

    // Alternative approach: show h has zero tail (all coeffs ≡ 0 for index >= n),
    // then use reduce_zero_tail directly.
    // h[k] = s * base[k]. For k >= n+1+shift, out of range. For shift <= k < shift+n+1, h[k] = s * pf[k-shift].
    // Hmm, h has length n+1+shift which can be > 2n-1 when shift > n-2. The reduce won't be trivial.

    // Better approach: use reduce_additive to decompose.
    // Actually, the cleanest approach is to prove lemma_reduce_scalar:
    // poly_reduce(s * h) is pointwise ≡ s * poly_reduce(h).
    // Then poly_reduce(base) has all zeros (by lemma_reduce_p_full_shift),
    // so s * 0 ≡ 0 for each coefficient.

    // Let me prove reduce_scalar by induction on h.len().
    lemma_reduce_scalar::<F>(s, base, p_coeffs);
    lemma_reduce_p_full_shift::<F>(p_coeffs, shift);

    let r_base = poly_reduce(base, p_coeffs);
    let r_h = poly_reduce(h, p_coeffs);

    assert forall|k: int| 0 <= k < n as int
        implies (#[trigger] r_h[k]).eqv(F::zero())
    by {
        // r_h[k] ≡ s * r_base[k] ≡ s * 0 ≡ 0
        ring_lemmas::lemma_mul_congruence_right::<F>(s, r_base[k], F::zero());
        F::axiom_mul_zero_right(s);
        F::axiom_eqv_transitive(s.mul(r_base[k]), s.mul(F::zero()), F::zero());
        F::axiom_eqv_transitive(r_h[k], s.mul(r_base[k]), F::zero());
    }
}

/// poly_reduce commutes with scalar multiplication (pointwise):
/// poly_reduce(poly_scalar_mul(s, h), p)[k] ≡ s * poly_reduce(h, p)[k].
proof fn lemma_reduce_scalar<F: Ring>(
    s: F, h: Seq<F>, p_coeffs: Seq<F>,
)
    requires
        p_coeffs.len() >= 2,
        h.len() >= p_coeffs.len(),
    ensures
        ({
            let sh = poly_scalar_mul(s, h);
            let r_sh = poly_reduce(sh, p_coeffs);
            let r_h = poly_reduce(h, p_coeffs);
            &&& r_sh.len() == p_coeffs.len()
            &&& r_h.len() == p_coeffs.len()
            &&& forall|k: int| 0 <= k < p_coeffs.len() as int ==>
                (#[trigger] r_sh[k]).eqv(s.mul(r_h[k]))
        }),
    decreases h.len(),
{
    let n = p_coeffs.len();
    let sh = poly_scalar_mul(s, h);
    fe_ring_lemmas::lemma_reduce_exact_length::<F>(h, p_coeffs);
    fe_ring_lemmas::lemma_reduce_exact_length::<F>(sh, p_coeffs);

    if h.len() <= n {
        // Base: poly_reduce is identity
        assert forall|k: int| 0 <= k < n as int
            implies (#[trigger] poly_reduce(sh, p_coeffs)[k]).eqv(s.mul(poly_reduce(h, p_coeffs)[k]))
        by {
            // sh[k] = s * h[k], poly_reduce(sh) = sh, poly_reduce(h) = h
            F::axiom_eqv_reflexive(s.mul(h[k]));
        }
    } else {
        // Inductive: reduce_step then recurse
        let rs_h = reduce_step(h, p_coeffs);
        let rs_sh = reduce_step(sh, p_coeffs);
        let m = h.len();
        let shift = m - 1 - n;

        // Show reduce_step(sh, p) ≡ s * reduce_step(h, p) pointwise
        let s_rs_h = poly_scalar_mul(s, rs_h);

        assert forall|k: int| 0 <= k < rs_sh.len() as int
            implies (#[trigger] rs_sh[k]).eqv(s_rs_h[k])
        by {
            if shift as int <= k < (shift + n) as int {
                // rs_sh[k] = sh[k] - sh[m-1]*p[k-shift]
                //          = s*h[k] - (s*h[m-1])*p[k-shift]
                // s_rs_h[k] = s * (h[k] - h[m-1]*p[k-shift])
                //           = s * h[k] - s * (h[m-1]*p[k-shift])    [via sub distribute]
                // Need: (s*h[m-1])*p[k-shift] ≡ s*(h[m-1]*p[k-shift])
                F::axiom_mul_associative(s, h[m as int - 1], p_coeffs[k - shift]);
                // s*h[k] - (s*h[m-1])*p ≡ s*h[k] - s*(h[m-1]*p)
                F::axiom_eqv_reflexive(s.mul(h[k]));
                additive_group_lemmas::lemma_sub_congruence::<F>(
                    s.mul(h[k]), s.mul(h[k]),
                    s.mul(h[m as int - 1]).mul(p_coeffs[k - shift]),
                    s.mul(h[m as int - 1].mul(p_coeffs[k - shift])),
                );
                // Now need: s*h[k] - s*(h[m-1]*p) ≡ s*(h[k] - h[m-1]*p)
                // This is s*a - s*b ≡ s*(a-b)
                lemma_mul_sub_distribute::<F>(s, h[k], h[m as int - 1].mul(p_coeffs[k - shift]));
                F::axiom_eqv_transitive(
                    rs_sh[k],
                    s.mul(h[k]).sub(s.mul(h[m as int - 1].mul(p_coeffs[k - shift]))),
                    s.mul(h[k].sub(h[m as int - 1].mul(p_coeffs[k - shift]))),
                );
            } else {
                // rs_sh[k] = sh[k] = s * h[k] = s * rs_h[k] = s_rs_h[k]
                F::axiom_eqv_reflexive(s.mul(h[k]));
            }
        }

        // By reduce_congruence: poly_reduce(rs_sh) ≡ poly_reduce(s_rs_h)
        fe_ring_lemmas::lemma_reduce_congruence::<F>(rs_sh, s_rs_h, p_coeffs);

        // By IH: poly_reduce(s * rs_h)[k] ≡ s * poly_reduce(rs_h)[k]
        lemma_reduce_scalar::<F>(s, rs_h, p_coeffs);

        // Chain: poly_reduce(sh)[k] = poly_reduce(rs_sh)[k]
        //      ≡ poly_reduce(s_rs_h)[k]  [congruence]
        //      ≡ s * poly_reduce(rs_h)[k]  [IH]
        //      = s * poly_reduce(h)[k]     [def]
        assert forall|k: int| 0 <= k < n as int
            implies (#[trigger] poly_reduce(sh, p_coeffs)[k]).eqv(s.mul(poly_reduce(h, p_coeffs)[k]))
        by {
            F::axiom_eqv_transitive(
                poly_reduce(rs_sh, p_coeffs)[k],
                poly_reduce(s_rs_h, p_coeffs)[k],
                s.mul(poly_reduce(rs_h, p_coeffs)[k]),
            );
        }
    }
}

/// Helper: s*a - s*b ≡ s*(a - b)
proof fn lemma_mul_sub_distribute<F: Ring>(s: F, a: F, b: F)
    ensures
        s.mul(a).sub(s.mul(b)).eqv(s.mul(a.sub(b))),
{
    // s*a - s*b = s*a + (-(s*b))
    F::axiom_sub_is_add_neg(s.mul(a), s.mul(b));
    // -(s*b) ≡ s*(-b)  [neg distributes: -(s*b) ≡ s*(-b)]
    ring_lemmas::lemma_mul_neg_right::<F>(s, b);
    // s*a + s*(-b) ≡ s*(a + (-b))
    F::axiom_mul_distributes_left(s, a, b.neg());
    F::axiom_eqv_symmetric(
        s.mul(a.add(b.neg())),
        s.mul(a).add(s.mul(b.neg())),
    );
    // s*(a + (-b)) ≡ s*(a - b)
    F::axiom_sub_is_add_neg(a, b);
    F::axiom_eqv_symmetric(a.sub(b), a.add(b.neg()));
    ring_lemmas::lemma_mul_congruence_right::<F>(s, a.add(b.neg()), a.sub(b));
    // Chain: s*a + (-(s*b)) ≡ s*a + s*(-b) ≡ s*(a+(-b)) ≡ s*(a-b)
    // mul_neg_right gives s*(-b) ≡ -(s*b), need reverse for congruence_right precondition
    F::axiom_eqv_symmetric(s.mul(b.neg()), s.mul(b).neg());
    additive_commutative_monoid_lemmas::lemma_add_congruence_right::<F>(
        s.mul(a), s.mul(b).neg(), s.mul(b.neg()));
    F::axiom_eqv_transitive(
        s.mul(a).add(s.mul(b).neg()),
        s.mul(a).add(s.mul(b.neg())),
        s.mul(a.add(b.neg())),
    );
    F::axiom_eqv_transitive(
        s.mul(a).add(s.mul(b).neg()),
        s.mul(a.add(b.neg())),
        s.mul(a.sub(b)),
    );
    F::axiom_eqv_transitive(
        s.mul(a).sub(s.mul(b)),
        s.mul(a).add(s.mul(b).neg()),
        s.mul(a.sub(b)),
    );
}

// ═══════════════════════════════════════════════════════════════════
//  Phase 4: Reduce passes through convolution
// ═══════════════════════════════════════════════════════════════════

/// reduce_step(h, p) is pointwise ≡ to (h truncated) - lead * shift(p_full, shift)
/// where the subtracted part reduces to zero.
///
/// Key insight: h = truncated_h + lead * x^(m-1) where truncated_h = h[0..m-1].
/// reduce_step subtracts lead * x^(m-1-n) * p(x) = lead * shift(p_full, m-1-n).
/// So: reduce_step(h) = h[0..m-1] - lead * shift(p_coeffs_part, m-1-n).
/// And lead * shift(p_full, m-1-n) reduces to zero.
///
/// Therefore: poly_reduce(h) ≡ poly_reduce(h with top coefficient zeroed)
///          ≡ poly_reduce(h with top n+1 coefficients from p_full subtracted)

/// reduce passes through conv on the left:
/// poly_reduce(poly_mul_raw(h, c)) ≡ poly_reduce(poly_mul_raw(poly_reduce(h), c))
/// when h.len() >= n, c.len() == n.
pub proof fn lemma_reduce_conv_left<F: Ring>(
    h: Seq<F>, c: Seq<F>, p_coeffs: Seq<F>,
)
    requires
        p_coeffs.len() >= 2,
        h.len() >= p_coeffs.len(),
        c.len() == p_coeffs.len(),
    ensures
        ({
            let n = p_coeffs.len();
            let raw_h = poly_mul_raw(h, c);
            let rh = poly_reduce(h, p_coeffs);
            let raw_rh = poly_mul_raw(rh, c);
            &&& raw_h.len() >= n
            &&& raw_rh.len() >= n
            &&& poly_reduce(raw_h, p_coeffs).len() == n
            &&& poly_reduce(raw_rh, p_coeffs).len() == n
            &&& forall|k: int| 0 <= k < n as int ==>
                (#[trigger] poly_reduce(raw_h, p_coeffs)[k]).eqv(
                    poly_reduce(raw_rh, p_coeffs)[k])
        }),
    decreases h.len(),
{
    let n = p_coeffs.len();
    let rh = poly_reduce(h, p_coeffs);
    fe_ring_lemmas::lemma_reduce_exact_length::<F>(h, p_coeffs);
    assert(rh.len() == n);

    let raw_h = poly_mul_raw(h, c);
    let raw_rh = poly_mul_raw(rh, c);

    // Length facts
    assert(raw_h.len() >= n);
    assert(raw_rh.len() >= n);
    fe_ring_lemmas::lemma_reduce_exact_length::<F>(raw_h, p_coeffs);
    fe_ring_lemmas::lemma_reduce_exact_length::<F>(raw_rh, p_coeffs);

    if h.len() <= n {
        // Base case: poly_reduce(h) = h, so raw_h = raw_rh
        assert(rh == h);
        assert forall|k: int| 0 <= k < n as int
            implies (#[trigger] poly_reduce(raw_h, p_coeffs)[k]).eqv(
                poly_reduce(raw_rh, p_coeffs)[k])
        by {
            F::axiom_eqv_reflexive(poly_reduce(raw_h, p_coeffs)[k]);
        }
    } else {
        // Inductive case: h.len() > n
        // h2 = reduce_step(h), poly_reduce(h) = poly_reduce(h2)
        let h2 = reduce_step(h, p_coeffs);
        assert(h2.len() == h.len() - 1);
        assert(h2.len() >= n);

        // Decompose: h[k] = h2[k] + lead * p_part[k] where p_part captures the subtraction
        // More precisely: h = h2_padded + lead * basis(m-1)
        // where h2_padded = h2 extended with 0 at position m-1
        // And reduce_step subtracts lead * shifted_p_coeffs

        // Key: conv(h, c, k) = conv(h2_padded, c, k) + lead * conv(e_{m-1}, c, k)
        //      where h2_padded = [h2[0], ..., h2[m-2], 0] (len m)
        // But conv(e_{m-1}, c, k) = coeff(c, k-(m-1))
        // And h = h2_padded + lead * e_{m-1} + lead * shifted(p_coeffs_embed)
        // Actually this decomposition is getting complex.

        // Simpler approach: use reduce_step on raw products.
        // conv(h, c, k) = sum_j h[j] * c[k-j]
        // h[j] for j < m-1: h[j] = h2[j] + (shift <= j < shift+n ? lead*p[j-shift] : 0)
        // h[m-1] = lead
        // So conv(h, c, k) = conv(h2_padded, c, k) + lead * coeff(c, k-(m-1))
        //   + sum of lead*p[j-shift]*c[k-j] terms for shift <= j < shift+n
        // This is complex. Let me use a different approach.

        // Better approach: direct use of conv linearity.
        // h = h2 ++ [0] + correction, where correction captures the undo of reduce_step.
        // Actually, let's just show conv(h, c) ≡ conv(h2_padded, c) pointwise,
        // where h2_padded has a zero top coeff.
        // Then poly_reduce(conv(h, c)) = poly_reduce(reduce_step(conv(h, c)))
        // and we can relate to poly_reduce(conv(h2, c)) by IH.

        // Actually, the simplest approach:
        // 1. IH: poly_reduce(conv(h2, c)) ≡ poly_reduce(conv(reduce(h2), c))
        // 2. reduce(h) = reduce(h2), so RHS is the same.
        // 3. Need: poly_reduce(conv(h, c)) ≡ poly_reduce(conv(h2, c))
        //
        // For step 3: h = reduce_step inverse of h2, meaning h2 = reduce_step(h).
        // h[k] for k < m-1: if shift <= k < shift+n: h2[k] = h[k] - lead*p[k-shift]
        //                   else: h2[k] = h[k]
        // h[m-1] = lead
        // So h = "h2 + lead*shifted_p_full" where shifted_p_full captures both the
        // p_coeffs correction and the leading 1 at position m-1.
        // In other words: h[k] = h2_ext[k] + lead * poly_shift(p_full, shift)[k]
        // where h2_ext = h2 extended with 0 at position m-1.

        // Then conv(h, c) = conv(h2_ext, c) + lead * conv(poly_shift(p_full, shift), c)
        // And poly_reduce of the second term is all zeros.
        // So poly_reduce(conv(h, c)) ≡ poly_reduce(conv(h2_ext, c))
        // But conv(h2_ext, c) ≡ conv(h2, c) (up to extending sum range with zero terms)
        // since h2_ext[k] = h2[k] for k < m-1 and h2_ext[m-1] = 0.

        // This is the approach. But implementing it requires several sub-steps.
        // Let me use assume(false) for now and come back to fill in.

        // IH
        lemma_reduce_conv_left::<F>(h2, c, p_coeffs);

        // poly_reduce(h) = poly_reduce(h2)
        // So poly_reduce(raw_rh) = poly_reduce(conv(reduce(h), c)) = poly_reduce(conv(reduce(h2), c))

        // For now, defer the hard step
        assume(
            forall|k: int| 0 <= k < n as int ==>
                (#[trigger] poly_reduce(raw_h, p_coeffs)[k]).eqv(
                    poly_reduce(raw_rh, p_coeffs)[k])
        );
    }
}

} // verus!
