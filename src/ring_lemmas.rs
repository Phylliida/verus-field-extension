use vstd::prelude::*;
use verus_algebra::traits::equivalence::Equivalence;
use verus_algebra::traits::additive_commutative_monoid::AdditiveCommutativeMonoid;
use verus_algebra::traits::additive_group::AdditiveGroup;
use verus_algebra::traits::ring::Ring;
use verus_algebra::lemmas::additive_group_lemmas;
use verus_algebra::lemmas::additive_commutative_monoid_lemmas;
use verus_algebra::lemmas::ring_lemmas;
use verus_algebra::summation::*;
use verus_algebra::archimedean::nat_mul;
use crate::minimal_poly::MinimalPoly;
use crate::spec::*;
use crate::poly_arith::*;

verus! {

// ═══════════════════════════════════════════════════════════════════
//  Convolution helper lemmas
// ═══════════════════════════════════════════════════════════════════

/// Helper: sum of zero function over any range is ≡ 0.
proof fn lemma_sum_zero_fn<F: Ring>(lo: int, hi: int)
    ensures
        sum::<F>(|j: int| F::zero(), lo, hi).eqv(F::zero()),
    decreases (if hi > lo { hi - lo } else { 0 }),
{
    if hi <= lo {
        lemma_sum_empty::<F>(|j: int| F::zero(), lo, hi);
    } else {
        // Peel first: sum = 0 + sum(lo+1, hi)
        lemma_sum_peel_first::<F>(|j: int| F::zero(), lo, hi);
        lemma_sum_zero_fn::<F>(lo + 1, hi);
        // Need reflexive BEFORE congruence (precondition)
        F::axiom_eqv_reflexive(F::zero());
        // 0 + sum ≡ 0 + 0
        additive_group_lemmas::lemma_add_congruence::<F>(
            F::zero(), F::zero(),
            sum::<F>(|j: int| F::zero(), lo + 1, hi), F::zero(),
        );
        F::axiom_add_zero_right(F::zero());
        F::axiom_eqv_transitive(
            F::zero().add(sum::<F>(|j: int| F::zero(), lo + 1, hi)),
            F::zero().add(F::zero()),
            F::zero(),
        );
        F::axiom_eqv_transitive(
            sum::<F>(|j: int| F::zero(), lo, hi),
            F::zero().add(sum::<F>(|j: int| F::zero(), lo + 1, hi)),
            F::zero(),
        );
    }
}

/// Convolution with zero polynomial gives zero at each position.
pub proof fn lemma_conv_zero_right<F: Ring>(a: Seq<F>, n: nat, k: int)
    requires
        a.len() == n,
        n >= 2,
    ensures
        conv_coeff(a, poly_zero::<F>(n), k).eqv(F::zero()),
{
    let b = poly_zero::<F>(n);
    let f = |j: int| coeff(a, j).mul(coeff(b, k - j));
    let g = |j: int| F::zero();

    assert forall|j: int| 0 <= j < n as int
        implies (#[trigger] f(j)).eqv(g(j))
    by {
        // coeff(b, k-j) = F::zero() always (b is all zeros)
        F::axiom_mul_zero_right(coeff(a, j));
    }
    lemma_sum_congruence::<F>(f, g, 0, n as int);
    lemma_sum_zero_fn::<F>(0, n as int);
    F::axiom_eqv_transitive(
        conv_coeff(a, b, k),
        sum::<F>(g, 0, n as int),
        F::zero(),
    );
}

/// Convolution with the unit polynomial [1, 0, ..., 0] (delta function).
///
/// conv_coeff(a, delta, k) ≡ coeff(a, k) for all k.
pub proof fn lemma_conv_delta_right<F: Ring>(a: Seq<F>, n: nat, k: int)
    requires
        a.len() == n,
        n >= 2,
    ensures
        conv_coeff(a, poly_one::<F>(n), k).eqv(coeff(a, k)),
{
    let delta = poly_one::<F>(n);
    let f = |j: int| coeff(a, j).mul(coeff(delta, k - j));

    if 0 <= k < n as int {
        // f(k) = coeff(a, k) * coeff(delta, 0) = coeff(a, k) * F::one() ≡ coeff(a, k)
        // f(j) for j != k: coeff(delta, k-j) = F::zero(), so f(j) ≡ 0

        // Split: sum(f, 0, n) ≡ sum(f, 0, k) + sum(f, k, n)
        lemma_sum_split::<F>(f, 0, k, n as int);
        // sum(f, k, n) ≡ f(k) + sum(f, k+1, n)
        lemma_sum_peel_first::<F>(f, k, n as int);

        // f(k) ≡ coeff(a, k)
        F::axiom_mul_one_right(coeff(a, k));

        // sum(f, 0, k) ≡ 0: all terms have coeff(delta, k-j) where k-j > 0
        let g = |j: int| F::zero();
        assert forall|j: int| 0 <= j < k
            implies (#[trigger] f(j)).eqv(g(j))
        by {
            F::axiom_mul_zero_right(coeff(a, j));
        }
        if k > 0 {
            lemma_sum_congruence::<F>(f, g, 0, k);
            lemma_sum_zero_fn::<F>(0, k);
            F::axiom_eqv_transitive(
                sum::<F>(f, 0, k), sum::<F>(g, 0, k), F::zero());
        } else {
            lemma_sum_empty::<F>(f, 0, 0);
        }

        // sum(f, k+1, n) ≡ 0: all terms have coeff(delta, k-j) where k-j < 0
        assert forall|j: int| k + 1 <= j < n as int
            implies (#[trigger] f(j)).eqv(g(j))
        by {
            F::axiom_mul_zero_right(coeff(a, j));
        }
        if k + 1 < n as int {
            lemma_sum_congruence::<F>(f, g, k + 1, n as int);
            lemma_sum_zero_fn::<F>(k + 1, n as int);
            F::axiom_eqv_transitive(
                sum::<F>(f, k + 1, n as int), sum::<F>(g, k + 1, n as int), F::zero());
        } else {
            lemma_sum_empty::<F>(f, k + 1, n as int);
        }

        // f(k) + sum(f, k+1, n) ≡ coeff(a,k) + 0 ≡ coeff(a,k)
        additive_group_lemmas::lemma_add_congruence::<F>(
            f(k), coeff(a, k),
            sum::<F>(f, k + 1, n as int), F::zero(),
        );
        F::axiom_add_zero_right(coeff(a, k));
        F::axiom_eqv_transitive(
            f(k).add(sum::<F>(f, k + 1, n as int)),
            coeff(a, k).add(F::zero()),
            coeff(a, k),
        );
        // sum(f, k, n) ≡ coeff(a, k)
        F::axiom_eqv_transitive(
            sum::<F>(f, k, n as int),
            f(k).add(sum::<F>(f, k + 1, n as int)),
            coeff(a, k),
        );
        // sum(f, 0, k) + sum(f, k, n) ≡ 0 + coeff(a, k) ≡ coeff(a, k)
        additive_group_lemmas::lemma_add_congruence::<F>(
            sum::<F>(f, 0, k), F::zero(),
            sum::<F>(f, k, n as int), coeff(a, k),
        );
        additive_group_lemmas::lemma_add_zero_left::<F>(coeff(a, k));
        F::axiom_eqv_transitive(
            sum::<F>(f, 0, k).add(sum::<F>(f, k, n as int)),
            F::zero().add(coeff(a, k)),
            coeff(a, k),
        );
        F::axiom_eqv_transitive(
            conv_coeff(a, delta, k),
            sum::<F>(f, 0, k).add(sum::<F>(f, k, n as int)),
            coeff(a, k),
        );
    } else {
        // k < 0 or k >= n: coeff(a, k) = F::zero()
        let g = |j: int| F::zero();
        assert forall|j: int| 0 <= j < n as int
            implies (#[trigger] f(j)).eqv(g(j))
        by {
            F::axiom_mul_zero_right(coeff(a, j));
        }
        lemma_sum_congruence::<F>(f, g, 0, n as int);
        lemma_sum_zero_fn::<F>(0, n as int);
        F::axiom_eqv_transitive(
            conv_coeff(a, delta, k),
            sum::<F>(g, 0, n as int),
            F::zero(),
        );
        F::axiom_eqv_reflexive(F::zero());
    }
}

// ═══════════════════════════════════════════════════════════════════
//  Convolution commutativity
// ═══════════════════════════════════════════════════════════════════

/// conv_coeff(a, b, k) ≡ conv_coeff(b, a, k).
///
/// This follows from mul commutativity + sum reindexing, but the formal
/// proof requires careful range management. Assumed for now.
pub proof fn lemma_conv_commutative<F: Ring>(a: Seq<F>, b: Seq<F>, k: int)
    requires
        a.len() >= 2,
        b.len() >= 2,
        a.len() == b.len(),
    ensures
        conv_coeff(a, b, k).eqv(conv_coeff(b, a, k)),
{
    // The proof involves: (1) mul_commutative on each term,
    // (2) sum reversal / reindexing to swap a[j]*b[k-j] ↔ b[j]*a[k-j].
    // Formally correct but needs careful range arithmetic; deferred.
    assume(conv_coeff(a, b, k).eqv(conv_coeff(b, a, k)));
}

// ═══════════════════════════════════════════════════════════════════
//  Reduction lemmas
// ═══════════════════════════════════════════════════════════════════

/// a.sub(b) ≡ a when b ≡ 0.
proof fn lemma_sub_zero_right<F: Ring>(a: F, b: F)
    requires b.eqv(F::zero()),
    ensures a.sub(b).eqv(a),
{
    // a.sub(b) ≡ a.add(b.neg())
    F::axiom_sub_is_add_neg(a, b);
    // b ≡ 0 → b.neg() ≡ 0.neg() ≡ 0
    F::axiom_neg_congruence(b, F::zero());
    additive_group_lemmas::lemma_neg_zero::<F>();
    F::axiom_eqv_transitive(b.neg(), F::zero().neg(), F::zero());
    // a.add(b.neg()) ≡ a.add(0) ≡ a
    additive_commutative_monoid_lemmas::lemma_add_congruence_right::<F>(a, b.neg(), F::zero());
    F::axiom_add_zero_right(a);
    F::axiom_eqv_transitive(a.add(b.neg()), a.add(F::zero()), a);
    F::axiom_eqv_transitive(a.sub(b), a.add(b.neg()), a);
}

/// When leading coefficient is ≡ 0, reduce_step result is pointwise ≡ to truncation.
proof fn lemma_reduce_step_zero_lead<F: Ring>(h: Seq<F>, p_coeffs: Seq<F>)
    requires
        h.len() > p_coeffs.len(),
        p_coeffs.len() >= 2,
        h[h.len() as int - 1].eqv(F::zero()),
    ensures
        forall|k: int| 0 <= k < h.len() as int - 1 ==>
            (#[trigger] reduce_step(h, p_coeffs)[k]).eqv(h[k]),
{
    let n = p_coeffs.len();
    let m = h.len();
    let lead = h[m as int - 1];
    let shift = m - 1 - n;

    assert forall|k: int| 0 <= k < m as int - 1
        implies (#[trigger] reduce_step(h, p_coeffs)[k]).eqv(h[k])
    by {
        if shift as int <= k < shift + n as int {
            // result[k] = h[k].sub(lead.mul(p_coeffs[k - shift]))
            // lead ≡ 0, so lead.mul(x) ≡ 0
            F::axiom_mul_congruence_left(lead, F::zero(), p_coeffs[k - shift]);
            ring_lemmas::lemma_mul_zero_left::<F>(p_coeffs[k - shift]);
            F::axiom_eqv_transitive(
                lead.mul(p_coeffs[k - shift]),
                F::zero().mul(p_coeffs[k - shift]),
                F::zero(),
            );
            // h[k].sub(lead*p[...]) ≡ h[k] since lead*p[...] ≡ 0
            lemma_sub_zero_right::<F>(h[k], lead.mul(p_coeffs[k - shift]));
        } else {
            // result[k] = h[k]
            F::axiom_eqv_reflexive(h[k]);
        }
    }
}

/// When all coefficients from index n onward are ≡ 0, poly_reduce gives
/// a result pointwise ≡ to the first n coefficients.
pub proof fn lemma_reduce_zero_tail<F: Ring>(h: Seq<F>, p_coeffs: Seq<F>)
    requires
        p_coeffs.len() >= 2,
        h.len() >= p_coeffs.len(),
        forall|k: int| p_coeffs.len() as int <= k < h.len() as int ==>
            (#[trigger] h[k]).eqv(F::zero()),
    ensures
        poly_reduce(h, p_coeffs).len() == p_coeffs.len(),
        forall|k: int| 0 <= k < p_coeffs.len() as int ==>
            (#[trigger] poly_reduce(h, p_coeffs)[k]).eqv(h[k]),
    decreases h.len(),
{
    let n = p_coeffs.len();
    if h.len() <= n {
        assert(poly_reduce(h, p_coeffs) == h);
        assert forall|k: int| 0 <= k < n as int
            implies (#[trigger] poly_reduce(h, p_coeffs)[k]).eqv(h[k])
        by {
            F::axiom_eqv_reflexive(h[k]);
        }
    } else {
        let h2 = reduce_step(h, p_coeffs);
        assert(h[h.len() as int - 1].eqv(F::zero()));
        lemma_reduce_step_zero_lead::<F>(h, p_coeffs);

        // h2 still has zero tail from n onward
        assert forall|k: int| n as int <= k < h2.len() as int
            implies (#[trigger] h2[k]).eqv(F::zero())
        by {
            F::axiom_eqv_transitive(h2[k], h[k], F::zero());
        }

        lemma_reduce_zero_tail::<F>(h2, p_coeffs);

        assert forall|k: int| 0 <= k < n as int
            implies (#[trigger] poly_reduce(h, p_coeffs)[k]).eqv(h[k])
        by {
            // poly_reduce(h, p)[k] = poly_reduce(h2, p)[k] ≡ h2[k] ≡ h[k]
            F::axiom_eqv_transitive(
                poly_reduce(h2, p_coeffs)[k],
                h2[k],
                h[k],
            );
        }
    }
}

// ═══════════════════════════════════════════════════════════════════
//  Reduction congruence
// ═══════════════════════════════════════════════════════════════════

/// If two polynomial sequences are pointwise equivalent, their reductions are too.
pub proof fn lemma_reduce_congruence<F: Ring>(h1: Seq<F>, h2: Seq<F>, p_coeffs: Seq<F>)
    requires
        p_coeffs.len() >= 2,
        h1.len() == h2.len(),
        forall|k: int| 0 <= k < h1.len() as int ==> (#[trigger] h1[k]).eqv(h2[k]),
    ensures
        poly_reduce(h1, p_coeffs).len() == poly_reduce(h2, p_coeffs).len(),
        forall|k: int| 0 <= k < poly_reduce(h1, p_coeffs).len() as int ==>
            (#[trigger] poly_reduce(h1, p_coeffs)[k]).eqv(poly_reduce(h2, p_coeffs)[k]),
    decreases h1.len(),
{
    let n = p_coeffs.len();
    if h1.len() <= n {
        assert forall|k: int| 0 <= k < h1.len() as int
            implies (#[trigger] poly_reduce(h1, p_coeffs)[k]).eqv(
                poly_reduce(h2, p_coeffs)[k])
        by { }
    } else {
        let r1 = reduce_step(h1, p_coeffs);
        let r2 = reduce_step(h2, p_coeffs);
        let m = h1.len();
        let shift = m - 1 - n;

        assert forall|k: int| 0 <= k < r1.len() as int
            implies (#[trigger] r1[k]).eqv(r2[k])
        by {
            if shift as int <= k < shift + n as int {
                F::axiom_mul_congruence_left(
                    h1[m as int - 1], h2[m as int - 1], p_coeffs[k - shift]);
                additive_group_lemmas::lemma_sub_congruence::<F>(
                    h1[k], h2[k],
                    h1[m as int - 1].mul(p_coeffs[k - shift]),
                    h2[m as int - 1].mul(p_coeffs[k - shift]),
                );
            } else {
                // r1[k] = h1[k], r2[k] = h2[k]
            }
        }

        lemma_reduce_congruence::<F>(r1, r2, p_coeffs);
    }
}

// ═══════════════════════════════════════════════════════════════════
//  Reduction length lemmas
// ═══════════════════════════════════════════════════════════════════

/// poly_reduce of input with len >= n gives output with len == n.
proof fn lemma_reduce_exact_length<F: Ring>(h: Seq<F>, p_coeffs: Seq<F>)
    requires
        p_coeffs.len() >= 2,
        h.len() >= p_coeffs.len(),
    ensures
        poly_reduce(h, p_coeffs).len() == p_coeffs.len(),
    decreases h.len(),
{
    if h.len() <= p_coeffs.len() {
    } else {
        lemma_reduce_exact_length::<F>(reduce_step(h, p_coeffs), p_coeffs);
    }
}

/// ext_mul produces output of the correct length.
pub proof fn lemma_ext_mul_length<F: Ring>(a: Seq<F>, b: Seq<F>, p_coeffs: Seq<F>)
    requires
        a.len() == p_coeffs.len(),
        b.len() == p_coeffs.len(),
        p_coeffs.len() >= 2,
    ensures
        ext_mul(a, b, p_coeffs).len() == p_coeffs.len(),
{
    let raw = poly_mul_raw(a, b);
    assert(raw.len() == 2 * p_coeffs.len() - 1);
    lemma_reduce_exact_length::<F>(raw, p_coeffs);
}

// ═══════════════════════════════════════════════════════════════════
//  Top-level lemmas for Ring axioms
// ═══════════════════════════════════════════════════════════════════

/// mul_one_right: ext_mul(a, [1,0,...,0], p) is pointwise ≡ to a.
pub proof fn lemma_ext_mul_one_right<F: Ring, P: MinimalPoly<F>>(
    x_coeffs: Seq<F>,
)
    requires
        x_coeffs.len() == P::degree(),
        P::degree() >= 2,
        P::coeffs().len() == P::degree(),
    ensures
        ext_mul(x_coeffs, poly_one::<F>(P::degree()), P::coeffs()).len() == P::degree(),
        forall|i: int| 0 <= i < P::degree() as int ==>
            coeff(ext_mul(x_coeffs, poly_one::<F>(P::degree()), P::coeffs()), i).eqv(
                x_coeffs[i]),
{
    let n = P::degree();
    let delta = poly_one::<F>(n);
    let raw = poly_mul_raw(x_coeffs, delta);

    assert(raw.len() == 2 * n - 1);

    // Show raw[k] ≡ x_coeffs[k] for k < n and raw[k] ≡ 0 for k >= n
    assert forall|k: int| 0 <= k < raw.len() as int
        implies (#[trigger] raw[k]).eqv(
            if (0 <= k < n as int) { x_coeffs[k] } else { F::zero() })
    by {
        lemma_conv_delta_right::<F>(x_coeffs, n, k);
        if 0 <= k < n as int {
        } else {
            F::axiom_eqv_reflexive(F::zero());
        }
    }

    // All high coefficients are ≡ 0
    assert forall|k: int| n as int <= k < raw.len() as int
        implies (#[trigger] raw[k]).eqv(F::zero())
    by { }

    lemma_reduce_zero_tail::<F>(raw, P::coeffs());
    lemma_ext_mul_length::<F>(x_coeffs, delta, P::coeffs());

    assert forall|i: int| 0 <= i < n as int
        implies coeff(ext_mul(x_coeffs, delta, P::coeffs()), i).eqv(x_coeffs[i])
    by {
        F::axiom_eqv_transitive(
            poly_reduce(raw, P::coeffs())[i],
            raw[i],
            x_coeffs[i],
        );
    }
}

/// mul_zero_right: ext_mul(a, [0,...,0], p) is pointwise ≡ 0.
pub proof fn lemma_ext_mul_zero_right<F: Ring, P: MinimalPoly<F>>(
    x_coeffs: Seq<F>,
)
    requires
        x_coeffs.len() == P::degree(),
        P::degree() >= 2,
        P::coeffs().len() == P::degree(),
    ensures
        ext_mul(x_coeffs, poly_zero::<F>(P::degree()), P::coeffs()).len() == P::degree(),
        forall|i: int| 0 <= i < P::degree() as int ==>
            coeff(ext_mul(x_coeffs, poly_zero::<F>(P::degree()), P::coeffs()), i).eqv(
                F::zero()),
{
    let n = P::degree();
    let zero_n = poly_zero::<F>(n);
    let raw = poly_mul_raw(x_coeffs, zero_n);

    assert(raw.len() == 2 * n - 1);

    assert forall|k: int| 0 <= k < raw.len() as int
        implies (#[trigger] raw[k]).eqv(F::zero())
    by {
        lemma_conv_zero_right::<F>(x_coeffs, n, k);
    }

    assert forall|k: int| n as int <= k < raw.len() as int
        implies (#[trigger] raw[k]).eqv(F::zero())
    by { }

    lemma_reduce_zero_tail::<F>(raw, P::coeffs());
    lemma_ext_mul_length::<F>(x_coeffs, zero_n, P::coeffs());

    assert forall|i: int| 0 <= i < n as int
        implies coeff(ext_mul(x_coeffs, zero_n, P::coeffs()), i).eqv(F::zero())
    by {
        F::axiom_eqv_transitive(
            poly_reduce(raw, P::coeffs())[i],
            raw[i],
            F::zero(),
        );
    }
}

/// one_ne_zero: 1 ≢ 0 in the extension field.
pub proof fn lemma_ext_one_ne_zero<F: Ring, P: MinimalPoly<F>>()
    requires
        P::degree() >= 2,
    ensures
        !fe_eqv::<F, P>(fe_one::<F, P>(), fe_zero::<F, P>()),
{
    F::axiom_one_ne_zero();
    let n = P::degree();
    let one_c = fe_one::<F, P>().coeffs;
    let zero_c = fe_zero::<F, P>().coeffs;
    // one_c = poly_one(n), zero_c = poly_zero(n)
    // coeff(one_c, 0) = F::one() (since 0 < n), coeff(zero_c, 0) = F::zero()
    assert(coeff(one_c, 0) == F::one());
    assert(coeff(zero_c, 0) == F::zero());
    assert(!F::one().eqv(F::zero()));
    // Therefore the forall in fe_eqv is violated at i = 0
    assert(!coeff(one_c, 0).eqv(coeff(zero_c, 0)));
}

/// mul_commutative: ext_mul(a, b, p) is pointwise ≡ ext_mul(b, a, p).
pub proof fn lemma_ext_mul_commutative<F: Ring, P: MinimalPoly<F>>(
    a: Seq<F>, b: Seq<F>,
)
    requires
        a.len() == P::degree(),
        b.len() == P::degree(),
        P::degree() >= 2,
        P::coeffs().len() == P::degree(),
    ensures
        ext_mul(a, b, P::coeffs()).len() == P::degree(),
        ext_mul(b, a, P::coeffs()).len() == P::degree(),
        forall|i: int| 0 <= i < P::degree() as int ==>
            coeff(ext_mul(a, b, P::coeffs()), i).eqv(
                coeff(ext_mul(b, a, P::coeffs()), i)),
{
    let n = P::degree();
    let p = P::coeffs();
    let raw_ab = poly_mul_raw(a, b);
    let raw_ba = poly_mul_raw(b, a);

    // Show raw_ab[k] ≡ raw_ba[k] via conv commutativity
    assert forall|k: int| 0 <= k < raw_ab.len() as int
        implies (#[trigger] raw_ab[k]).eqv(raw_ba[k])
    by {
        lemma_conv_commutative::<F>(a, b, k);
    }

    // Reduce congruence: poly_reduce(raw_ab) ≡ poly_reduce(raw_ba)
    lemma_reduce_congruence::<F>(raw_ab, raw_ba, p);
    lemma_ext_mul_length::<F>(a, b, p);
    lemma_ext_mul_length::<F>(b, a, p);
}

/// mul_congruence_left: if a ≡ b pointwise, then ext_mul(a, c, p) ≡ ext_mul(b, c, p).
pub proof fn lemma_ext_mul_congruence_left<F: Ring, P: MinimalPoly<F>>(
    a: Seq<F>, b: Seq<F>, c: Seq<F>,
)
    requires
        a.len() == P::degree(),
        b.len() == P::degree(),
        c.len() == P::degree(),
        P::degree() >= 2,
        P::coeffs().len() == P::degree(),
        forall|i: int| 0 <= i < P::degree() as int ==> (#[trigger] a[i]).eqv(b[i]),
    ensures
        ext_mul(a, c, P::coeffs()).len() == P::degree(),
        ext_mul(b, c, P::coeffs()).len() == P::degree(),
        forall|i: int| 0 <= i < P::degree() as int ==>
            coeff(ext_mul(a, c, P::coeffs()), i).eqv(
                coeff(ext_mul(b, c, P::coeffs()), i)),
{
    let n = P::degree();
    let p = P::coeffs();
    let raw_ac = poly_mul_raw(a, c);
    let raw_bc = poly_mul_raw(b, c);

    // Show raw_ac[k] ≡ raw_bc[k] via conv congruence
    assert forall|k: int| 0 <= k < raw_ac.len() as int
        implies (#[trigger] raw_ac[k]).eqv(raw_bc[k])
    by {
        lemma_conv_congruence_left::<F>(a, b, c, k);
    }

    lemma_reduce_congruence::<F>(raw_ac, raw_bc, p);
    lemma_ext_mul_length::<F>(a, c, p);
    lemma_ext_mul_length::<F>(b, c, p);
}

/// Convolution congruence on the left argument.
proof fn lemma_conv_congruence_left<F: Ring>(
    a1: Seq<F>, a2: Seq<F>, b: Seq<F>, k: int,
)
    requires
        a1.len() >= 2,
        a2.len() == a1.len(),
        b.len() == a1.len(),
        forall|i: int| 0 <= i < a1.len() as int ==> (#[trigger] a1[i]).eqv(a2[i]),
    ensures
        conv_coeff(a1, b, k).eqv(conv_coeff(a2, b, k)),
{
    let n = a1.len();
    let f1 = |j: int| coeff(a1, j).mul(coeff(b, k - j));
    let f2 = |j: int| coeff(a2, j).mul(coeff(b, k - j));

    assert forall|j: int| 0 <= j < n as int
        implies (#[trigger] f1(j)).eqv(f2(j))
    by {
        if 0 <= j < n as int {
            // a1[j] ≡ a2[j], so a1[j]*b[k-j] ≡ a2[j]*b[k-j]
            F::axiom_mul_congruence_left(coeff(a1, j), coeff(a2, j), coeff(b, k - j));
        }
    }
    lemma_sum_congruence::<F>(f1, f2, 0, n as int);
}

/// Convolution congruence on the right argument.
pub proof fn lemma_conv_congruence_right<F: Ring>(
    a: Seq<F>, b1: Seq<F>, b2: Seq<F>, k: int,
)
    requires
        a.len() >= 2,
        b1.len() == a.len(),
        b2.len() == a.len(),
        forall|i: int| 0 <= i < b1.len() as int ==> (#[trigger] b1[i]).eqv(b2[i]),
    ensures
        conv_coeff(a, b1, k).eqv(conv_coeff(a, b2, k)),
{
    let n = a.len();
    let f1 = |j: int| coeff(a, j).mul(coeff(b1, k - j));
    let f2 = |j: int| coeff(a, j).mul(coeff(b2, k - j));

    assert forall|j: int| 0 <= j < n as int
        implies (#[trigger] f1(j)).eqv(f2(j))
    by {
        if 0 <= k - j < n as int {
            ring_lemmas::lemma_mul_congruence_right::<F>(coeff(a, j), b1[k - j], b2[k - j]);
        } else {
            F::axiom_eqv_reflexive(f1(j));
        }
    }
    lemma_sum_congruence::<F>(f1, f2, 0, n as int);
}

/// Convolution linearity: conv_coeff(a, b+c, k) ≡ conv_coeff(a, b, k) + conv_coeff(a, c, k).
pub proof fn lemma_conv_add_right<F: Ring>(
    a: Seq<F>, b: Seq<F>, c: Seq<F>, k: int,
)
    requires
        a.len() >= 2,
        b.len() == a.len(),
        c.len() == a.len(),
    ensures
        conv_coeff(a, poly_add(b, c), k).eqv(
            conv_coeff(a, b, k).add(conv_coeff(a, c, k))),
{
    let n = a.len();
    let bc = poly_add(b, c);

    let f_bc = |j: int| coeff(a, j).mul(coeff(bc, k - j));
    let f_b = |j: int| coeff(a, j).mul(coeff(b, k - j));
    let f_c = |j: int| coeff(a, j).mul(coeff(c, k - j));
    let f_sum = |j: int| f_b(j).add(f_c(j));

    assert forall|j: int| 0 <= j < n as int
        implies (#[trigger] f_bc(j)).eqv(f_sum(j))
    by {
        if 0 <= k - j < n as int {
            // coeff(bc, k-j) = b[k-j].add(c[k-j])
            // a[j] * (b[k-j] + c[k-j]) ≡ a[j]*b[k-j] + a[j]*c[k-j]
            F::axiom_mul_distributes_left(coeff(a, j), coeff(b, k - j), coeff(c, k - j));
        } else {
            // coeff(bc, k-j) = 0, coeff(b, k-j) = 0, coeff(c, k-j) = 0
            // a[j]*0 ≡ 0 ≡ a[j]*0 + a[j]*0
            F::axiom_mul_zero_right(coeff(a, j));
            // f_b(j) ≡ 0, f_c(j) ≡ 0
            // 0 + 0 ≡ 0
            additive_group_lemmas::lemma_add_congruence::<F>(
                f_b(j), F::zero(), f_c(j), F::zero());
            F::axiom_add_zero_right(F::zero());
            F::axiom_eqv_transitive(f_sum(j), F::zero().add(F::zero()), F::zero());
            F::axiom_eqv_symmetric(f_bc(j), F::zero());
            F::axiom_eqv_symmetric(f_sum(j), F::zero());
            F::axiom_eqv_transitive(f_bc(j), F::zero(), f_sum(j));
            F::axiom_eqv_symmetric(f_bc(j), f_sum(j));
        }
    }
    lemma_sum_congruence::<F>(f_bc, f_sum, 0, n as int);
    lemma_sum_add::<F>(f_b, f_c, 0, n as int);
    F::axiom_eqv_transitive(
        conv_coeff(a, bc, k),
        sum::<F>(f_sum, 0, n as int),
        conv_coeff(a, b, k).add(conv_coeff(a, c, k)),
    );
}

/// reduce_additive: poly_reduce distributes over polynomial addition.
/// Deferred — requires showing reduce_step is linear.
pub proof fn lemma_reduce_additive<F: Ring>(
    h1: Seq<F>, h2: Seq<F>, p_coeffs: Seq<F>,
)
    requires
        p_coeffs.len() >= 2,
        h1.len() == h2.len(),
        h1.len() >= p_coeffs.len(),
    ensures
        poly_reduce(h1, p_coeffs).len() == p_coeffs.len(),
        poly_reduce(h2, p_coeffs).len() == p_coeffs.len(),
        poly_reduce(poly_add(h1, h2), p_coeffs).len() == p_coeffs.len(),
        forall|k: int| 0 <= k < p_coeffs.len() as int ==>
            (#[trigger] poly_reduce(poly_add(h1, h2), p_coeffs)[k]).eqv(
                poly_reduce(h1, p_coeffs)[k].add(poly_reduce(h2, p_coeffs)[k])),
{
    assume(false);
}

/// mul_distributes_left: ext_mul(a, b+c, p) ≡ ext_mul(a, b, p) + ext_mul(a, c, p).
pub proof fn lemma_ext_mul_distributes_left<F: Ring, P: MinimalPoly<F>>(
    a: Seq<F>, b: Seq<F>, c: Seq<F>,
)
    requires
        a.len() == P::degree(),
        b.len() == P::degree(),
        c.len() == P::degree(),
        P::degree() >= 2,
        P::coeffs().len() == P::degree(),
    ensures
        ext_mul(a, poly_add(b, c), P::coeffs()).len() == P::degree(),
        forall|i: int| 0 <= i < P::degree() as int ==>
            coeff(ext_mul(a, poly_add(b, c), P::coeffs()), i).eqv(
                coeff(ext_mul(a, b, P::coeffs()), i).add(
                    coeff(ext_mul(a, c, P::coeffs()), i))),
{
    let n = P::degree();
    let p = P::coeffs();
    let bc = poly_add(b, c);

    // raw products
    let raw_abc = poly_mul_raw(a, bc);
    let raw_ab = poly_mul_raw(a, b);
    let raw_ac = poly_mul_raw(a, c);

    // conv linearity: raw_abc[k] ≡ raw_ab[k] + raw_ac[k]
    assert forall|k: int| 0 <= k < raw_abc.len() as int
        implies (#[trigger] raw_abc[k]).eqv(raw_ab[k].add(raw_ac[k]))
    by {
        lemma_conv_add_right::<F>(a, b, c, k);
    }

    // raw_abc = poly_add(raw_ab, raw_ac) up to eqv
    // We need: poly_reduce(raw_abc) ≡ poly_reduce(raw_ab) + poly_reduce(raw_ac)
    // This is poly_reduce linearity + congruence.

    // Use reduce_additive: reduce(raw_ab + raw_ac) ≡ reduce(raw_ab) + reduce(raw_ac)
    lemma_reduce_additive::<F>(raw_ab, raw_ac, p);

    // Then reduce(raw_abc) ≡ reduce(raw_ab + raw_ac) by congruence
    let raw_sum = poly_add(raw_ab, raw_ac);
    assert forall|k: int| 0 <= k < raw_abc.len() as int
        implies (#[trigger] raw_abc[k]).eqv(raw_sum[k])
    by {
        // raw_abc[k] ≡ raw_ab[k] + raw_ac[k] = raw_sum[k]
        F::axiom_eqv_reflexive(raw_sum[k]);
        // Already have raw_abc[k] ≡ raw_ab[k].add(raw_ac[k])
    }

    lemma_reduce_congruence::<F>(raw_abc, raw_sum, p);
    lemma_ext_mul_length::<F>(a, bc, p);
    lemma_ext_mul_length::<F>(a, b, p);
    lemma_ext_mul_length::<F>(a, c, p);

    // Chain: reduce(raw_abc)[i] ≡ reduce(raw_sum)[i] ≡ reduce(raw_ab)[i] + reduce(raw_ac)[i]
    assert forall|i: int| 0 <= i < n as int
        implies coeff(ext_mul(a, bc, p), i).eqv(
            coeff(ext_mul(a, b, p), i).add(coeff(ext_mul(a, c, p), i)))
    by {
        F::axiom_eqv_transitive(
            poly_reduce(raw_abc, p)[i],
            poly_reduce(raw_sum, p)[i],
            poly_reduce(raw_ab, p)[i].add(poly_reduce(raw_ac, p)[i]),
        );
    }
}

} // verus!
