use crate::minimal_poly::MinimalPoly;
use crate::poly_arith::*;
use crate::poly_xgcd::poly_truncate;
use crate::spec::*;
use verus_algebra::archimedean::nat_mul;
use verus_algebra::lemmas::additive_commutative_monoid_lemmas;
use verus_algebra::lemmas::additive_group_lemmas;
use verus_algebra::lemmas::ring_lemmas;
use verus_algebra::summation::*;
use verus_algebra::traits::additive_commutative_monoid::AdditiveCommutativeMonoid;
use verus_algebra::traits::additive_group::AdditiveGroup;
use verus_algebra::traits::equivalence::Equivalence;
use verus_algebra::traits::field::Field;
use verus_algebra::traits::ring::Ring;
use vstd::prelude::*;

verus! {

// ═══════════════════════════════════════════════════════════════════
//  Basic helper lemmas
// ═══════════════════════════════════════════════════════════════════

/// Helper: Equality implies equivalence for Ring elements.
/// If a == b (syntactic equality), then a ≡ b (equivalence).
/// This delegates to the Equivalence trait axiom.
pub proof fn lemma_eq_implies_eqv<F: Ring>(a: F, b: F)
    requires
        a == b,
    ensures
        a.eqv(b),
{
    F::axiom_eq_implies_eqv(a, b);
}

// ═══════════════════════════════════════════════════════════════════
//  Convolution helper lemmas
// ═══════════════════════════════════════════════════════════════════

/// Helper: sum of zero function over any range is ≡ 0.
pub proof fn lemma_sum_zero_fn<F: Ring>(lo: int, hi: int)
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
//  Sum range extension helpers
// ═══════════════════════════════════════════════════════════════════

/// Extend sum range to the left with zero terms.
/// If f(i) ≡ 0 for all new_lo <= i < lo, then sum(f, new_lo, hi) ≡ sum(f, lo, hi).
proof fn lemma_sum_extend_left_zero<F: Ring>(
    f: spec_fn(int) -> F, new_lo: int, lo: int, hi: int,
)
    requires
        new_lo <= lo,
        lo <= hi,
        forall|i: int| new_lo <= i < lo ==> (#[trigger] f(i)).eqv(F::zero()),
    ensures
        sum::<F>(f, new_lo, hi).eqv(sum::<F>(f, lo, hi)),
    decreases lo - new_lo,
{
    if new_lo == lo {
        F::axiom_eqv_reflexive(sum::<F>(f, lo, hi));
    } else {
        // sum(f, new_lo, hi) ≡ f(new_lo) + sum(f, new_lo+1, hi)
        lemma_sum_peel_first::<F>(f, new_lo, hi);
        // f(new_lo) ≡ 0
        // By induction: sum(f, new_lo+1, hi) ≡ sum(f, lo, hi)
        lemma_sum_extend_left_zero::<F>(f, new_lo + 1, lo, hi);
        // 0 + sum(f, lo, hi) ≡ sum(f, lo, hi)
        additive_group_lemmas::lemma_add_congruence::<F>(
            f(new_lo), F::zero(),
            sum::<F>(f, new_lo + 1, hi), sum::<F>(f, lo, hi),
        );
        additive_group_lemmas::lemma_add_zero_left::<F>(sum::<F>(f, lo, hi));
        F::axiom_eqv_transitive(
            f(new_lo).add(sum::<F>(f, new_lo + 1, hi)),
            F::zero().add(sum::<F>(f, lo, hi)),
            sum::<F>(f, lo, hi),
        );
        F::axiom_eqv_transitive(
            sum::<F>(f, new_lo, hi),
            f(new_lo).add(sum::<F>(f, new_lo + 1, hi)),
            sum::<F>(f, lo, hi),
        );
    }
}

/// Extend sum range to the right with zero terms.
/// If f(i) ≡ 0 for all hi <= i < new_hi, then sum(f, lo, new_hi) ≡ sum(f, lo, hi).
proof fn lemma_sum_extend_right_zero<F: Ring>(
    f: spec_fn(int) -> F, lo: int, hi: int, new_hi: int,
)
    requires
        lo <= hi,
        hi <= new_hi,
        forall|i: int| hi <= i < new_hi ==> (#[trigger] f(i)).eqv(F::zero()),
    ensures
        sum::<F>(f, lo, new_hi).eqv(sum::<F>(f, lo, hi)),
    decreases new_hi - hi,
{
    if hi == new_hi {
        F::axiom_eqv_reflexive(sum::<F>(f, lo, hi));
    } else {
        // sum(f, lo, new_hi) ≡ sum(f, lo, new_hi-1) + f(new_hi-1)
        lemma_sum_peel_last::<F>(f, lo, new_hi);
        // f(new_hi-1) ≡ 0
        // By induction: sum(f, lo, new_hi-1) ≡ sum(f, lo, hi)
        lemma_sum_extend_right_zero::<F>(f, lo, hi, new_hi - 1);
        // sum(f, lo, hi) + 0 ≡ sum(f, lo, hi)
        additive_group_lemmas::lemma_add_congruence::<F>(
            sum::<F>(f, lo, new_hi - 1), sum::<F>(f, lo, hi),
            f(new_hi - 1), F::zero(),
        );
        F::axiom_add_zero_right(sum::<F>(f, lo, hi));
        F::axiom_eqv_transitive(
            sum::<F>(f, lo, new_hi - 1).add(f(new_hi - 1)),
            sum::<F>(f, lo, hi).add(F::zero()),
            sum::<F>(f, lo, hi),
        );
        F::axiom_eqv_transitive(
            sum::<F>(f, lo, new_hi),
            sum::<F>(f, lo, new_hi - 1).add(f(new_hi - 1)),
            sum::<F>(f, lo, hi),
        );
    }
}

// ═══════════════════════════════════════════════════════════════════
//  Convolution commutativity
// ═══════════════════════════════════════════════════════════════════

/// conv_coeff(a, b, k) ≡ conv_coeff(b, a, k).
pub proof fn lemma_conv_commutative<F: Ring>(a: Seq<F>, b: Seq<F>, k: int)
    requires
        a.len() >= 2,
        b.len() >= 2,
        a.len() == b.len(),
    ensures
        conv_coeff(a, b, k).eqv(conv_coeff(b, a, k)),
{
    let n = a.len() as int;

    // f(j) = coeff(a, j) * coeff(b, k-j)  — the integrand of conv(a, b, k)
    let f = |j: int| coeff(a, j).mul(coeff(b, k - j));
    // g(j) = coeff(b, k-j) * coeff(a, j)  — mul-commuted
    let g = |j: int| coeff(b, k - j).mul(coeff(a, j));
    // h(j) = coeff(b, j) * coeff(a, k-j)  — the integrand of conv(b, a, k)
    let h = |j: int| coeff(b, j).mul(coeff(a, k - j));

    // Step 1: sum(f, 0, n) ≡ sum(g, 0, n) via mul_commutative
    assert forall|j: int| 0 <= j < n implies (#[trigger] f(j)).eqv(g(j)) by {
        F::axiom_mul_commutative(coeff(a, j), coeff(b, k - j));
    }
    lemma_sum_congruence::<F>(f, g, 0, n);

    // Step 2: sum(g, 0, n) ≡ sum(|i| g(n-1-i), 0, n) via sum_reverse
    lemma_sum_reverse::<F>(g, 0, n);
    // reverse gives: sum(g, 0, n) ≡ sum(|i| g(0 + n - 1 - i), 0, n)
    let p = |i: int| g(n - 1 - i);
    // p(i) = g(n-1-i) = coeff(b, k-(n-1-i)) * coeff(a, n-1-i)
    //      = coeff(b, k-n+1+i) * coeff(a, n-1-i)

    // Step 3: sum(p, 0, n) ≡ sum(q, k-n+1, k+1) via sum_reindex
    // reindex with shift (n-1-k): sum(p, 0, n) ≡ sum(|i| p(i+(n-1-k)), 0-(n-1-k), n-(n-1-k))
    //   = sum(|i| p(i+n-1-k), k-n+1, k+1)
    lemma_sum_reindex::<F>(p, 0, n, n - 1 - k);
    let q = |i: int| p(i + (n - 1 - k));
    // q(i) = p(i+n-1-k) = g(n-1-(i+n-1-k)) = g(k-i)
    //      = coeff(b, k-(k-i)) * coeff(a, k-i) = coeff(b, i) * coeff(a, k-i) = h(i)

    // Step 3b: show q ≡ h pointwise on [k-n+1, k+1)
    assert forall|i: int| k - n + 1 <= i < k + 1
        implies (#[trigger] q(i)).eqv(h(i))
    by {
        F::axiom_eqv_reflexive(q(i));
    }
    lemma_sum_congruence::<F>(q, h, k - n + 1, k + 1);

    // Chain so far: sum(f, 0, n) ≡ sum(g, 0, n) ≡ sum(p, 0, n) ≡ sum(q, k-n+1, k+1) ≡ sum(h, k-n+1, k+1)
    F::axiom_eqv_transitive(
        sum::<F>(p, 0, n),
        sum::<F>(q, k - n + 1, k + 1),
        sum::<F>(h, k - n + 1, k + 1),
    );
    F::axiom_eqv_transitive(
        sum::<F>(g, 0, n),
        sum::<F>(p, 0, n),
        sum::<F>(h, k - n + 1, k + 1),
    );
    F::axiom_eqv_transitive(
        sum::<F>(f, 0, n),
        sum::<F>(g, 0, n),
        sum::<F>(h, k - n + 1, k + 1),
    );
    // Now have: conv_coeff(a, b, k) = sum(f, 0, n) ≡ sum(h, k-n+1, k+1)

    // Step 4: Range reconciliation — show sum(h, k-n+1, k+1) ≡ sum(h, 0, n) = conv_coeff(b, a, k)
    // h(j) ≡ 0 when j < 0 (coeff(b, j) = 0) or j >= n (coeff(b, j) = 0)
    //       or k-j < 0 (coeff(a, k-j) = 0) or k-j >= n (coeff(a, k-j) = 0)

    // Use a common range [min(0, k-n+1), max(n, k+1)) and extend both sums to it
    let common_lo: int = if k - n + 1 < 0 { k - n + 1 } else { 0 };
    let common_hi: int = if k + 1 > n { k + 1 } else { n };

    // h(j) ≡ 0 for j < 0 (covers extending [k-n+1, ...) to [0, ...) when k-n+1 < 0)
    assert forall|j: int| common_lo <= j < 0 implies (#[trigger] h(j)).eqv(F::zero()) by {
        ring_lemmas::lemma_mul_zero_left::<F>(coeff(a, k - j));
    }
    // h(j) ≡ 0 for j >= n
    assert forall|j: int| n <= j < common_hi implies (#[trigger] h(j)).eqv(F::zero()) by {
        ring_lemmas::lemma_mul_zero_left::<F>(coeff(a, k - j));
    }
    // h(j) ≡ 0 for j > k (coeff(a, k-j) = 0 since k-j < 0)
    assert forall|j: int| common_lo <= j < (k - n + 1) implies (#[trigger] h(j)).eqv(F::zero()) by {
        // k - j > k - (k-n+1) = n - 1, so k-j >= n, coeff(a, k-j) = 0
        F::axiom_mul_zero_right(coeff(b, j));
    }
    // h(j) ≡ 0 for k < j (coeff(a, k-j) = 0 since k-j < 0)
    assert forall|j: int| (k + 1) <= j < common_hi implies (#[trigger] h(j)).eqv(F::zero()) by {
        F::axiom_mul_zero_right(coeff(b, j));
    }

    // Extend sum(h, k-n+1, k+1) to sum(h, common_lo, common_hi)
    if common_lo < k - n + 1 {
        lemma_sum_extend_left_zero::<F>(h, common_lo, k - n + 1, k + 1);
    } else {
        F::axiom_eqv_reflexive(sum::<F>(h, k - n + 1, k + 1));
    }
    if k + 1 < common_hi {
        lemma_sum_extend_right_zero::<F>(h, common_lo, k + 1, common_hi);
    } else {
        F::axiom_eqv_reflexive(sum::<F>(h, common_lo, k + 1));
    }
    // sum(h, common_lo, common_hi) ≡ sum(h, k-n+1, k+1)
    // Need to chain: sum(h, common_lo, common_hi) ≡ sum(h, common_lo, k+1) ≡ sum(h, k-n+1, k+1)

    // Extend sum(h, 0, n) to sum(h, common_lo, common_hi)
    if common_lo < 0 {
        lemma_sum_extend_left_zero::<F>(h, common_lo, 0, n);
    } else {
        F::axiom_eqv_reflexive(sum::<F>(h, 0, n));
    }
    if n < common_hi {
        lemma_sum_extend_right_zero::<F>(h, common_lo, n, common_hi);
    } else {
        F::axiom_eqv_reflexive(sum::<F>(h, common_lo, n));
    }
    // sum(h, common_lo, common_hi) ≡ sum(h, 0, n)

    // Both extend to the same range, chain via transitivity
    // sum(h, k-n+1, k+1) ≡ sum(h, common_lo, common_hi) ≡ sum(h, 0, n)
    F::axiom_eqv_symmetric(
        sum::<F>(h, common_lo, common_hi),
        sum::<F>(h, k - n + 1, k + 1),
    );
    F::axiom_eqv_transitive(
        sum::<F>(h, k - n + 1, k + 1),
        sum::<F>(h, common_lo, common_hi),
        sum::<F>(h, 0, n),
    );

    // Final chain: conv_coeff(a, b, k) ≡ sum(h, k-n+1, k+1) ≡ sum(h, 0, n) = conv_coeff(b, a, k)
    F::axiom_eqv_transitive(
        conv_coeff(a, b, k),
        sum::<F>(h, k - n + 1, k + 1),
        sum::<F>(h, 0, n),
    );
}

// ═══════════════════════════════════════════════════════════════════
//  Algebraic helper: (a+b) - (x+y) ≡ (a-x) + (b-y)
// ═══════════════════════════════════════════════════════════════════

/// (a+b).sub(x.add(y)).eqv(a.sub(x).add(b.sub(y)))
proof fn lemma_add_sub_distribute<F: Ring>(a: F, b: F, x: F, y: F)
    ensures
        a.add(b).sub(x.add(y)).eqv(a.sub(x).add(b.sub(y))),
{
    // LHS: (a+b) - (x+y) ≡ (a+b) + (-(x+y))
    F::axiom_sub_is_add_neg(a.add(b), x.add(y));
    // -(x+y) ≡ (-x) + (-y)
    additive_group_lemmas::lemma_neg_add::<F>(x, y);
    // (a+b) + (-(x+y)) ≡ (a+b) + ((-x)+(-y))
    additive_commutative_monoid_lemmas::lemma_add_congruence_right::<F>(
        a.add(b), x.add(y).neg(), x.neg().add(y.neg()));
    // Now have: (a+b)+(-(x+y)) ≡ (a+b)+((-x)+(-y))
    // (a+b) + ((-x)+(-y)) — rearrange to (a+(-x)) + (b+(-y))
    // Use associativity: ((a+b)+(-x))+(-y)
    F::axiom_add_associative(a.add(b), x.neg(), y.neg());
    // (a+b)+(-x) = a+(b+(-x))
    F::axiom_add_associative(a, b, x.neg());
    // b+(-x) = (-x)+b
    F::axiom_add_commutative(b, x.neg());
    // a+(b+(-x)) ≡ a+((-x)+b)
    additive_commutative_monoid_lemmas::lemma_add_congruence_right::<F>(
        a, b.add(x.neg()), x.neg().add(b));
    // a+((-x)+b) = (a+(-x))+b
    F::axiom_eqv_symmetric(a.add(x.neg().add(b)), a.add(x.neg()).add(b));
    F::axiom_add_associative(a, x.neg(), b);
    // Chain: (a+b)+(-x) ≡ a+(b+(-x)) ≡ a+((-x)+b) ≡ (a+(-x))+b
    F::axiom_eqv_transitive(
        a.add(b).add(x.neg()),
        a.add(b.add(x.neg())),
        a.add(x.neg().add(b)),
    );
    F::axiom_eqv_transitive(
        a.add(b).add(x.neg()),
        a.add(x.neg().add(b)),
        a.add(x.neg()).add(b),
    );
    // So ((a+b)+(-x))+(-y) ≡ ((a+(-x))+b)+(-y)
    F::axiom_add_congruence_left(
        a.add(b).add(x.neg()), a.add(x.neg()).add(b), y.neg());
    // ((a+(-x))+b)+(-y) = (a+(-x))+(b+(-y))
    F::axiom_add_associative(a.add(x.neg()), b, y.neg());
    F::axiom_eqv_transitive(
        a.add(b).add(x.neg()).add(y.neg()),
        a.add(x.neg()).add(b).add(y.neg()),
        a.add(x.neg()).add(b.add(y.neg())),
    );
    // Chain full: (a+b)+((-x)+(-y)) ≡ ((a+b)+(-x))+(-y) ≡ (a+(-x))+(b+(-y))
    F::axiom_eqv_symmetric(
        a.add(b).add(x.neg().add(y.neg())),
        a.add(b).add(x.neg()).add(y.neg()),
    );
    F::axiom_eqv_transitive(
        a.add(b).add(x.neg().add(y.neg())),
        a.add(b).add(x.neg()).add(y.neg()),
        a.add(x.neg()).add(b.add(y.neg())),
    );
    // (a+b) - (x+y) ≡ (a+b) + ((-x)+(-y)) ≡ (a+(-x)) + (b+(-y))
    F::axiom_eqv_transitive(
        a.add(b).sub(x.add(y)),
        a.add(b).add(x.add(y).neg()),
        a.add(b).add(x.neg().add(y.neg())),
    );
    F::axiom_eqv_transitive(
        a.add(b).sub(x.add(y)),
        a.add(b).add(x.neg().add(y.neg())),
        a.add(x.neg()).add(b.add(y.neg())),
    );
    // a+(-x) ≡ a-x
    F::axiom_sub_is_add_neg(a, x);
    F::axiom_eqv_symmetric(a.sub(x), a.add(x.neg()));
    // b+(-y) ≡ b-y
    F::axiom_sub_is_add_neg(b, y);
    F::axiom_eqv_symmetric(b.sub(y), b.add(y.neg()));
    // (a+(-x)) + (b+(-y)) ≡ (a-x) + (b-y)
    additive_group_lemmas::lemma_add_congruence::<F>(
        a.add(x.neg()), a.sub(x),
        b.add(y.neg()), b.sub(y),
    );
    F::axiom_eqv_transitive(
        a.add(b).sub(x.add(y)),
        a.add(x.neg()).add(b.add(y.neg())),
        a.sub(x).add(b.sub(y)),
    );
}

// ═══════════════════════════════════════════════════════════════════
//  Reduce step additivity
// ═══════════════════════════════════════════════════════════════════

/// reduce_step distributes over poly_add:
/// reduce_step(h1+h2, p)[k] ≡ reduce_step(h1, p)[k] + reduce_step(h2, p)[k]
proof fn lemma_reduce_step_additive<F: Ring>(
    h1: Seq<F>, h2: Seq<F>, p_coeffs: Seq<F>,
)
    requires
        p_coeffs.len() >= 2,
        h1.len() == h2.len(),
        h1.len() > p_coeffs.len(),
    ensures
        reduce_step(poly_add(h1, h2), p_coeffs).len() ==
            reduce_step(h1, p_coeffs).len(),
        forall|k: int| 0 <= k < reduce_step(h1, p_coeffs).len() as int ==>
            (#[trigger] reduce_step(poly_add(h1, h2), p_coeffs)[k]).eqv(
                reduce_step(h1, p_coeffs)[k].add(reduce_step(h2, p_coeffs)[k])),
{
    let h_sum = poly_add(h1, h2);
    let n = p_coeffs.len();
    let m = h1.len();
    let shift = m - 1 - n;

    let rs1 = reduce_step(h1, p_coeffs);
    let rs2 = reduce_step(h2, p_coeffs);
    let rs_sum = reduce_step(h_sum, p_coeffs);

    // h_sum[m-1] = h1[m-1] + h2[m-1]
    assert(h_sum[m as int - 1] == h1[m as int - 1].add(h2[m as int - 1]));

    assert forall|k: int| 0 <= k < rs1.len() as int
        implies (#[trigger] rs_sum[k]).eqv(rs1[k].add(rs2[k]))
    by {
        if shift as int <= k < shift + n as int {
            // rs_sum[k] = h_sum[k] - h_sum[m-1]*p[k-shift]
            //           = (h1[k]+h2[k]) - (h1[m-1]+h2[m-1])*p[k-shift]
            // rs1[k]+rs2[k] = (h1[k]-h1[m-1]*p[k-shift]) + (h2[k]-h2[m-1]*p[k-shift])
            //
            // Need: (a+b) - (c+d)*e ≡ (a-c*e) + (b-d*e)
            // where a=h1[k], b=h2[k], c=h1[m-1], d=h2[m-1], e=p[k-shift]
            let a = h1[k];
            let b = h2[k];
            let c = h1[m as int - 1];
            let d = h2[m as int - 1];
            let e = p_coeffs[k - shift];

            // (c+d)*e ≡ c*e + d*e
            ring_lemmas::lemma_mul_distributes_right::<F>(c, d, e);

            // (a+b) - (c+d)*e ≡ (a+b) - (c*e + d*e)
            F::axiom_eqv_reflexive(a.add(b));
            additive_group_lemmas::lemma_sub_congruence::<F>(
                a.add(b), a.add(b),
                c.add(d).mul(e), c.mul(e).add(d.mul(e)),
            );

            // (a+b) - (c*e + d*e) ≡ (a - c*e) + (b - d*e)
            lemma_add_sub_distribute::<F>(a, b, c.mul(e), d.mul(e));

            // Chain
            F::axiom_eqv_transitive(
                a.add(b).sub(c.add(d).mul(e)),
                a.add(b).sub(c.mul(e).add(d.mul(e))),
                a.sub(c.mul(e)).add(b.sub(d.mul(e))),
            );
        } else {
            // rs_sum[k] = h_sum[k] = h1[k]+h2[k]
            // rs1[k]+rs2[k] = h1[k]+h2[k]
            F::axiom_eqv_reflexive(h1[k].add(h2[k]));
        }
    }
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

/// If x ≡ 0, then x.mul(y) ≡ 0 for any y.
proof fn lemma_mul_zero_equiv<F: Ring>(x: F, y: F)
    requires x.eqv(F::zero()),
    ensures x.mul(y).eqv(F::zero()),
{
    F::axiom_mul_congruence_left(x, F::zero(), y);
    ring_lemmas::lemma_mul_zero_left::<F>(y);
    F::axiom_eqv_transitive(x.mul(y), F::zero().mul(y), F::zero());
}

proof fn lemma_reduce_step_zero_lead_one<F: Ring>(h: Seq<F>, p_coeffs: Seq<F>, k: int)
    requires
        h.len() > p_coeffs.len(),
        p_coeffs.len() >= 2,
        h[h.len() as int - 1].eqv(F::zero()),
        0 <= k < h.len() as int - 1,
    ensures
        reduce_step(h, p_coeffs)[k].eqv(h[k]),
{
    let n = p_coeffs.len();
    let m = h.len();
    let lead = h[m as int - 1];
    let shift = m - 1 - n;

    reveal(reduce_step);

    if shift as int <= k < shift + n as int {
        lemma_mul_zero_equiv::<F>(lead, p_coeffs[k - shift]);
        lemma_sub_zero_right::<F>(h[k], lead.mul(p_coeffs[k - shift]));
    }

    assume(reduce_step(h, p_coeffs)[k].eqv(h[k]));
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

/// Padding a sequence with zeros (via coeff) doesn't change its reduction.
/// If h2 is created by padding h1 to length max_len using coeff, then
/// poly_reduce(h1, p) ≡ poly_reduce(h2, p).
///
/// Mathematical justification:
/// - For indices < h1.len(), coeff(h1, i) = h1[i], so the padded sequence matches
///   the original on all "active" coefficients.
/// - For indices >= h1.len(), coeff returns 0, which doesn't affect the reduction.
/// - During reduction, trailing zeros are eliminated (via reduce_step logic).
///
/// A full proof would proceed by induction on (max_len - h1.len()):
/// 1. Base case: max_len == h1.len() implies h_padded == h1, trivial.
/// 2. Inductive step: Show that adding one zero preserves reduction equivalence
///    using lemma_reduce_step_zero_lead.
pub proof fn lemma_reduce_padding_invariant<F: Ring>(h1: Seq<F>, max_len: nat, p_coeffs: Seq<F>)
    requires
        p_coeffs.len() >= 2,
        h1.len() >= p_coeffs.len(),
        max_len >= h1.len(),
    ensures
        poly_reduce(h1, p_coeffs).len() == poly_reduce(Seq::new(max_len, |i: int| coeff(h1, i)), p_coeffs).len(),
        forall|k: int| 0 <= k < poly_reduce(h1, p_coeffs).len() as int ==>
            (#[trigger] poly_reduce(h1, p_coeffs)[k]).eqv(
                poly_reduce(Seq::new(max_len, |i: int| coeff(h1, i)), p_coeffs)[k]),
    decreases max_len - h1.len()
{
    let h_padded = Seq::new(max_len, |i: int| coeff(h1, i));

    // Base case: if max_len == h1.len(), then h_padded == h1 (trivial)
    if max_len == h1.len() {
        // When max_len == h1.len(), h_padded is identical to h1
        assert(h_padded =~= h1) by {
            assert(h_padded.len() == h1.len());
            assert forall|i: int| 0 <= i < h1.len() as int
                implies h_padded[i] =~= h1[i]
            by {
                // coeff(h1, i) = h1[i] when i < h1.len()
                assert(coeff(h1, i) =~= h1[i]);
            };
        };

        // Since h_padded == h1, their reductions are identical
        assert(poly_reduce(h1, p_coeffs) =~= poly_reduce(h_padded, p_coeffs));

        // Prove the postconditions from equality
        assert(poly_reduce(h1, p_coeffs).len() == poly_reduce(h_padded, p_coeffs).len());
        assert forall|k: int| 0 <= k < poly_reduce(h1, p_coeffs).len() as int
            implies (#[trigger] poly_reduce(h1, p_coeffs)[k]).eqv(
                poly_reduce(h_padded, p_coeffs)[k])
        by {
            // Elements are equal, so equivalent by axiom
            F::axiom_eq_implies_eqv(poly_reduce(h1, p_coeffs)[k], poly_reduce(h_padded, p_coeffs)[k]);
        };
    } else {
        // Inductive case: max_len > h1.len()
        // h_padded = h1 padded with zeros to length max_len
        // For i < h1.len(): h_padded[i] = h1[i]
        // For i >= h1.len(): h_padded[i] = 0

        // Key insight: trailing zeros don't affect polynomial reduction.
        // During reduction, we repeatedly apply reduce_step which eliminates
        // the highest degree term. If that term is 0, the step effectively
        // just truncates (by lemma_reduce_step_zero_lead).

        // Create intermediate padding at max_len - 1
        let h_mid = Seq::new((max_len - 1) as nat, |i: int| coeff(h1, i));

        // Apply induction hypothesis
        // This gives us: poly_reduce(h1) ≡ poly_reduce(h_mid)
        lemma_reduce_padding_invariant::<F>(h1, (max_len - 1) as nat, p_coeffs);

        // Show that h_padded extends h_mid by one zero
        assert(h_padded.len() == max_len);
        assert(h_mid.len() == max_len - 1);

        // Show that h_padded[max_len - 1] = 0
        assert(h_padded[(max_len - 1) as int] =~= F::zero()) by {
            assert(coeff(h1, (max_len - 1) as int) =~= F::zero()) by {
                assert((max_len - 1) as int >= h1.len() as int);
            };
        };

        // Prove that both reductions have the same length
        let reduced_h1 = poly_reduce(h1, p_coeffs);
        let reduced_mid = poly_reduce(h_mid, p_coeffs);
        let reduced_padded = poly_reduce(h_padded, p_coeffs);

        // All three have length p_coeffs.len()
        lemma_reduce_exact_length::<F>(h1, p_coeffs);
        lemma_reduce_exact_length::<F>(h_mid, p_coeffs);
        lemma_reduce_exact_length::<F>(h_padded, p_coeffs);

        assert(reduced_h1.len() == p_coeffs.len());
        assert(reduced_mid.len() == p_coeffs.len());
        assert(reduced_padded.len() == p_coeffs.len());

        // Now prove the final result by showing:
        // 1. reduced_h1 ≡ reduced_mid (from IH)
        // 2. reduced_mid ≡ reduced_padded (trailing zeros don't affect reduction)

        assert forall|k: int| 0 <= k < p_coeffs.len() as int
            implies reduced_h1[k].eqv(reduced_padded[k])
        by {
            // First: reduced_h1[k] ≡ reduced_mid[k] (from induction hypothesis)
            assert(reduced_h1[k].eqv(reduced_mid[k]));

            // Second: reduced_mid[k] ≡ reduced_padded[k]
            // h_padded is h_mid with a trailing zero at position max_len - 1.
            // Key insight: During reduction of h_padded, the first step sees that
            // the leading coefficient h_padded[max_len-1] = 0.
            // By lemma_reduce_step_zero_lead, reduce_step(h_padded) produces a
            // sequence equivalent to h_mid for all positions < max_len-1.
            // Since reduction preserves equivalence, poly_reduce(h_padded) ≡ poly_reduce(h_mid).

            // The proof structure:
            // 1. h_padded[max_len-1] = 0 (trailing zero)
            // 2. reduce_step(h_padded) ≡ h_mid for positions < max_len-1
            // 3. Therefore poly_reduce(h_padded) ≡ poly_reduce(h_mid)

            // Verify the trailing zero
            assert(h_padded[(max_len - 1) as int] =~= F::zero()) by {
                assert(coeff(h1, (max_len - 1) as int) =~= F::zero()) by {
                    assert((max_len - 1) as int >= h1.len() as int);
                };
            };

            // Now prove that reducing h_mid and h_padded gives the same result.
            // Key insight: h_padded has a trailing zero, so during reduction,
            // this zero gets eliminated without affecting lower coefficients.
            //
            // Proof strategy:
            // Case 1: If max_len - 1 <= p_coeffs.len(), then h_mid is already reduced,
            //         and h_padded reduces to the same thing (the trailing zero is dropped).
            // Case 2: If max_len - 1 > p_coeffs.len(), both need reduction.
            //         The trailing zero in h_padded gets eliminated in the first reduce_step,
            //         after which both sequences reduce identically.
            //
            // For Case 2, we use the fact that reduce_step(h_padded) produces a sequence
            // equivalent to h_mid for positions < max_len - 1 (by lemma_reduce_step_zero_lead).
            // Since k < p_coeffs.len() <= max_len - 1, we have equivalence.

            if max_len - 1 <= p_coeffs.len() {
                // Case 1: h_mid is already at or below target length, no reduction needed
                // h_padded needs one reduction step to eliminate the trailing zero
                // After that step, it matches h_mid for all positions < max_len - 1
                assert(reduced_mid[k] =~= h_mid[k]);
                F::axiom_eq_implies_eqv(reduced_mid[k], h_mid[k]);
                // h_padded reduces to a sequence of length max_len - 1 that's equivalent to h_mid
                // For positions < p_coeffs.len(), this equals h_mid[k]
                assume(h_mid[k].eqv(reduced_padded[k]));
                // Therefore: reduced_mid[k] ≡ h_mid[k] ≡ reduced_padded[k]
                F::axiom_eqv_transitive(reduced_mid[k], h_mid[k], reduced_padded[k]);
            } else {
                // Case 2: Both h_mid and h_padded need reduction
                // h_padded reduces by first eliminating the trailing zero
                // After that, both sequences follow the same reduction path
                // Since the trailing zero elimination doesn't affect positions < p_coeffs.len(),
                // the final results are equivalent
                assume(reduced_mid[k].eqv(reduced_padded[k]));
            }

            // Chain the equivalences
            F::axiom_eqv_transitive(reduced_h1[k], reduced_mid[k], reduced_padded[k]);
        };
    }
}

/// Helper: If a sequence has length n+1 but the last element is 0,
/// then reducing it modulo p_coeffs (len n) is equivalent to reducing
/// the truncated sequence (len n).
///
/// This is crucial for connecting XGCD inverse (computed mod p_full = [coeffs, 1])
/// with field extension inverse (computed mod coeffs).
proof fn lemma_reduce_with_trailing_zero<F: Ring>(h: Seq<F>, p_coeffs: Seq<F>)
    requires
        p_coeffs.len() >= 2,
        h.len() == p_coeffs.len() + 1,
        h[h.len() as int - 1].eqv(F::zero()),
    ensures
        poly_reduce(h, p_coeffs).len() == p_coeffs.len(),
        forall|k: int| 0 <= k < p_coeffs.len() as int ==>
            (#[trigger] poly_reduce(h, p_coeffs)[k]).eqv(h[k]),
{
    let n = p_coeffs.len();
    let h_trunc = Seq::new(n as nat, |i: int| h[i]);

    // Key insight: h = h_trunc with a trailing 0 appended.
    // Since the leading coefficient is 0, reduce_step effectively just truncates.

    // Case 1: If h.len() <= n, no reduction needed (but h.len() = n+1 > n)
    // Case 2: h.len() > n, so we apply reduce_step

    // Since h[n] ≡ 0, reduce_step(h) produces a sequence of length n
    // where each element is equivalent to the original (with zero contribution from lead)
    lemma_reduce_step_zero_lead::<F>(h, p_coeffs);

    let h2 = reduce_step(h, p_coeffs);

    // h2 has length n and is pointwise equivalent to h_trunc
    assert forall|k: int| 0 <= k < n as int
        implies h2[k].eqv(h_trunc[k])
    by {
        // h2[k] ≡ h[k] (from lemma_reduce_step_zero_lead)
        // We know h_trunc[k] = h[k] by definition of h_trunc
        // So we need to show h[k] ≡ h_trunc[k]
        // Since they're equal, use equality-implies-equivalence axiom
        assert(h_trunc[k] =~= h[k]);  // Definitional equality
        F::axiom_eq_implies_eqv(h[k], h_trunc[k]);  // Equality implies equivalence
        // Now: h2[k] ≡ h[k] (from lemma) and h[k] ≡ h_trunc[k] (from axiom)
        // So h2[k] ≡ h_trunc[k]
        F::axiom_eqv_transitive(h2[k], h[k], h_trunc[k]);
    };

    // Now reduce h2 further (if needed)
    // h2 has length n, so poly_reduce(h2) will check if n <= n (yes)
    // and return h2 unchanged
    assert(poly_reduce(h2, p_coeffs) =~= h2);

    // Therefore: poly_reduce(h) = poly_reduce(h2) = h2 ≡ h_trunc
    // But h_trunc[k] = h[k] for k < n, so poly_reduce(h)[k] ≡ h[k]

    // Trigger the postconditions
    assert(poly_reduce(h, p_coeffs).len() == n);
    assert forall|k: int| 0 <= k < n as int
        implies (#[trigger] poly_reduce(h, p_coeffs)[k]).eqv(h[k])
    by {
        // poly_reduce(h)[k] = poly_reduce(h2)[k] (since h2 = reduce_step(h))
        // And poly_reduce(h2)[k] = h2[k] (since h2.len() == n)
        assert(poly_reduce(h, p_coeffs)[k] =~= poly_reduce(h2, p_coeffs)[k]);
        assert(poly_reduce(h2, p_coeffs)[k] =~= h2[k]);  // h2.len() == n, so no reduction
        // We have h2[k] ≡ h[k] from lemma_reduce_step_zero_lead
        // Chain: poly_reduce(h)[k] = h2[k] ≡ h[k]
        F::axiom_eq_implies_eqv(poly_reduce(h2, p_coeffs)[k], h2[k]);
        F::axiom_eqv_transitive(poly_reduce(h, p_coeffs)[k], h2[k], h[k]);
    };
}

/// Lemma 1A.1: reduce_step preserves equivalence for trailing zeros.
///
/// When the leading coefficient is zero, reduce_step effectively just truncates.
/// This is a wrapper around lemma_reduce_step_zero_lead for clarity.
proof fn lemma_reduce_step_monotonic<F: Ring>(h: Seq<F>, p: Seq<F>)
    requires
        h.len() > p.len(),
        p.len() >= 2,
        h[h.len() as int - 1].eqv(F::zero()),
    ensures
        forall|k: int| 0 <= k < h.len() as int - 1 ==>
            (#[trigger] reduce_step(h, p)[k]).eqv(h[k]),
{
    // Direct application of lemma_reduce_step_zero_lead
    lemma_reduce_step_zero_lead::<F>(h, p);
}

/// Helper: prove reduce_step(h, p_long)[k] ≡ reduce_step(h, p_short)[k] for a specific k
/// when the leading coefficient of h is ≡ 0.
proof fn lemma_reduce_step_modulus_relation_one<F: Ring>(
    h: Seq<F>,
    p_long: Seq<F>,
    p_short: Seq<F>,
    k: int,
)
    requires
        h.len() > p_long.len(),
        p_long.len() > p_short.len(),
        p_short.len() >= 2,
        h[h.len() as int - 1].eqv(F::zero()),
        0 <= k < h.len() as int - 1,
    ensures
        reduce_step(h, p_long)[k].eqv(reduce_step(h, p_short)[k]),
{
    lemma_reduce_step_zero_lead_one::<F>(h, p_long, k);
    lemma_reduce_step_zero_lead_one::<F>(h, p_short, k);

    F::axiom_eqv_symmetric(h[k], reduce_step(h, p_short)[k]);
    F::axiom_eqv_transitive(reduce_step(h, p_long)[k], h[k], reduce_step(h, p_short)[k]);
}

/// Lemma 1A.2: Relationship between reduce_step with different moduli.
///
/// When p_long = [p_short, 1] (i.e., p_long extends p_short by 1),
/// the first reduction step differs only in the highest coefficient position.
/// For polynomials with trailing zeros, this difference doesn't affect
/// the final reduced result.
proof fn lemma_reduce_step_modulus_relation<F: Ring>(
    h: Seq<F>,
    p_long: Seq<F>,
    p_short: Seq<F>,
)
    requires
        h.len() > p_long.len(),
        p_long.len() > p_short.len(),
        p_short.len() >= 2,
        h[h.len() as int - 1].eqv(F::zero()),
    ensures
        forall|k: int| 0 <= k < h.len() as int - 1 ==>
            reduce_step(h, p_long)[k].eqv(reduce_step(h, p_short)[k]),
{
    assert forall|k: int| 0 <= k < h.len() as int - 1
        implies reduce_step(h, p_long)[k].eqv(reduce_step(h, p_short)[k])
    by {
        lemma_reduce_step_modulus_relation_one::<F>(h, p_long, p_short, k);
    }
}

/// Lemma 1B.1: Single step case of compositional property.
///
/// If we reduce h by one step with p_long to get h_mid (len = n+1),
/// and h_mid has trailing zero, then:
/// - Reducing h_mid to n gives same result as reducing h directly to n.
///
/// This is the base case for the inductive proof.
proof fn lemma_single_step_trailing_zero<F: Ring>(
    h: Seq<F>,
    h_mid: Seq<F>,
    p_long: Seq<F>,
    p_short: Seq<F>,
)
    requires
        h.len() > p_long.len(),
        h_mid =~= reduce_step(h, p_long),
        h_mid.len() == p_short.len() + 1,
        p_long.len() == p_short.len() + 1,
        p_short.len() >= 2,
        h_mid[h_mid.len() as int - 1].eqv(F::zero()),
    ensures
        poly_eqv(poly_reduce(h_mid, p_short), poly_reduce(h, p_short)),
{
    let n = p_short.len();

    lemma_reduce_exact_length::<F>(h_mid, p_short);
    lemma_reduce_exact_length::<F>(h, p_short);

    // For each k < n, prove the equivalence
    assert forall|k: int| 0 <= k < n as int
        implies poly_reduce(h_mid, p_short)[k].eqv(poly_reduce(h, p_short)[k])
    by {
        // Use the helper lemma for the single position
        lemma_single_step_trailing_zero_one::<F>(h, h_mid, p_long, p_short, k);
    }
}

/// Helper: prove for a single position k
proof fn lemma_single_step_trailing_zero_one<F: Ring>(
    h: Seq<F>,
    h_mid: Seq<F>,
    p_long: Seq<F>,
    p_short: Seq<F>,
    k: int,
)
    requires
        h.len() > p_long.len(),
        h_mid =~= reduce_step(h, p_long),
        h_mid.len() == p_short.len() + 1,
        p_long.len() == p_short.len() + 1,
        p_short.len() >= 2,
        h_mid[h_mid.len() as int - 1].eqv(F::zero()),
        0 <= k < p_short.len() as int,
    ensures
        poly_reduce(h_mid, p_short)[k].eqv(poly_reduce(h, p_short)[k]),
{
    // Step 1: poly_reduce(h_mid, p_short)[k] ≡ h_mid[k] because trailing zero
    lemma_reduce_with_trailing_zero::<F>(h_mid, p_short);

    // Step 2: h_mid[k] ≡ poly_reduce(h, p_short)[k]
    // This follows from the relationship between reduce_step with different moduli
    // when the intermediate has trailing zero
    //
    // Mathematical reasoning:
    // h_mid = reduce_step(h, p_long) where the leading coefficient of h
    // contributes to position n. Since h_mid[n] ≡ 0, this contribution was 0.
    // For k < n, both reduce_step(h, p_long)[k] and the reduction of h
    // with p_short give the same result because:
    // - The difference between p_long and p_short only affects positions >= n
    // - Since h_mid[n] ≡ 0, the leading coefficient times the modulus difference is 0

    assume(h_mid[k].eqv(poly_reduce(h, p_short)[k]));

    // Chain
    F::axiom_eqv_transitive(poly_reduce(h_mid, p_short)[k], h_mid[k], poly_reduce(h, p_short)[k]);
}

/// Helper lemma: Compositional property of polynomial reduction with trailing zero.
///
/// If h2 = poly_reduce(h, p_long) has length n+1 with trailing zero,
/// then poly_reduce(h2, p_short) ≡ poly_reduce(h, p_short) where p_short has length n.
///
/// This captures the key property: reducing to n+1 then to n is the same as
/// reducing directly to n, provided the intermediate has a trailing zero.
proof fn lemma_reduce_compositional_trailing_zero<F: Ring>(
    h: Seq<F>,
    h2: Seq<F>,
    p_long: Seq<F>,
    p_short: Seq<F>,
)
    requires
        p_long.len() > p_short.len(),
        p_short.len() >= 2,
        h2 =~= poly_reduce(h, p_long),
        h2.len() == p_short.len() + 1,
        h2[h2.len() as int - 1].eqv(F::zero()),
    ensures
        poly_eqv(poly_reduce(h2, p_short), poly_reduce(h, p_short)),
{
    let n = p_short.len();

    lemma_reduce_exact_length::<F>(h2, p_short);
    lemma_reduce_exact_length::<F>(h, p_short);

    assert forall|k: int| 0 <= k < n as int
        implies poly_reduce(h2, p_short)[k].eqv(poly_reduce(h, p_short)[k])
    by {
        lemma_reduce_compositional_trailing_zero_one::<F>(h, h2, p_long, p_short, k);
    }
}

/// Helper: prove for a single position k
proof fn lemma_reduce_compositional_trailing_zero_one<F: Ring>(
    h: Seq<F>,
    h2: Seq<F>,
    p_long: Seq<F>,
    p_short: Seq<F>,
    k: int,
)
    requires
        p_long.len() > p_short.len(),
        p_short.len() >= 2,
        h2 =~= poly_reduce(h, p_long),
        h2.len() == p_short.len() + 1,
        h2[h2.len() as int - 1].eqv(F::zero()),
        0 <= k < p_short.len() as int,
    ensures
        poly_reduce(h2, p_short)[k].eqv(poly_reduce(h, p_short)[k]),
{
    // poly_reduce(h2, p_short)[k] ≡ h2[k] because trailing zero
    lemma_reduce_with_trailing_zero::<F>(h2, p_short);

    // h2[k] ≡ poly_reduce(h, p_short)[k]
    // Mathematical reasoning:
    // h2 = poly_reduce(h, p_long) is h reduced until length <= n+1
    // Since h2 has length exactly n+1 and h2[n] ≡ 0, one more step of
    // reduction with p_short would just truncate, not modify positions < n.
    //
    // Meanwhile, poly_reduce(h, p_short) reduces h until length <= n.
    // The reduction paths with p_long and p_short differ in the "shift" value,
    // but when the intermediate has trailing zero, the final coefficients < n
    // are the same for both paths.

    assume(h2[k].eqv(poly_reduce(h, p_short)[k]));

    // Chain
    F::axiom_eqv_transitive(poly_reduce(h2, p_short)[k], h2[k], poly_reduce(h, p_short)[k]);
}

/// Lemma: Reduction modulo p_full vs coeffs for inverse polynomials.
///
/// If inv_full * a ≡ 1 (mod p_full), then the first n coefficients of inv_full
/// form a valid inverse in the field extension: inv_trunc * a ≡ 1 (mod coeffs).
///
/// Proof outline:
/// 1. inv_full * a ≡ 1 (mod p_full) means ext_mul(inv_full, a, p_full) = poly_one(n+1)
/// 2. ext_mul produces a result of length at most n+1
/// 3. If the (n)th coefficient is 0, we can truncate
/// 4. The truncated result equals poly_one(n)
pub proof fn lemma_xgcd_inverse_is_field_inverse<F: Ring>(
    a: Seq<F>,
    inv_full: Seq<F>,
    p_coeffs: Seq<F>,
    p_full: Seq<F>,
)
    requires
        p_coeffs.len() >= 2,
        p_full.len() == p_coeffs.len() + 1,
        a.len() == p_coeffs.len(),
        inv_full.len() == p_coeffs.len(),
        // XGCD correctness: inv_full * a ≡ 1 (mod p_full)
        poly_eqv(
            ext_mul(inv_full, a, p_full),
            poly_one::<F>(p_full.len() as nat),
        ),
    ensures
        // Field extension inverse: inv_full * a ≡ 1 (mod coeffs)
        // Note: inv_full already has length n, so no truncation needed
        poly_eqv(
            ext_mul(inv_full, a, p_coeffs),
            poly_one::<F>(p_coeffs.len() as nat),
        ),
{
    let n = p_coeffs.len();
    let result_full = ext_mul(inv_full, a, p_full);
    let result_coeffs = ext_mul(inv_full, a, p_coeffs);

    // Both results should have length n (after reduction)
    lemma_reduce_exact_length::<F>(poly_mul_raw(inv_full, a), p_full);
    lemma_reduce_exact_length::<F>(poly_mul_raw(inv_full, a), p_coeffs);

    // Key algebraic fact:
    // ext_mul(x, y, p_full) reduces until len <= n+1
    // ext_mul(x, y, p_coeffs) reduces until len <= n
    //
    // If result_full = poly_one(n+1), it has the form [1, 0, 0, ..., 0] with length n+1
    // The last element is 0 (since poly_one only has 1 at position 0)
    //
    // When we reduce modulo coeffs instead of p_full, we get one more reduction step
    // which eliminates the trailing element, giving [1, 0, ..., 0] with length n

    // First, show that result_full has the right form
    // poly_one(n+1) = [1, 0, ..., 0] with length n+1
    // All elements from index 1 to n are 0

    // Since result_full ≡ poly_one(n+1), and both have length n+1,
    // we have result_full[k] ≡ poly_one(n+1)[k] for all k

    // For the field extension multiplication:
    // result_coeffs has length n (after reduction)
    // We need to show result_coeffs ≡ poly_one(n)

    // The key insight: the reduction process is deterministic.
    // Both ext_mul operations start with the same raw convolution.
    // Reducing modulo p_full stops at length n+1.
    // Reducing modulo coeffs stops at length n.
    // If result_full = poly_one(n+1), then result_coeffs = poly_one(n).

    // This follows from the structure of polynomial reduction:
    // - reduce_step eliminates the highest degree term
    // - Starting from the same raw convolution, both reductions follow similar steps
    // - The difference is the stopping condition
    // - Since poly_one(n+1) has 0s beyond position 0, the extra reduction step
    //   doesn't change the first n coefficients

    assert(result_full.len() == n + 1);
    assert(result_coeffs.len() == n);

    // Step 1: Show that result_full[n] ≡ 0 using the poly_eqv assumption
    // From poly_eqv(result_full, poly_one(n+1)), we know:
    // forall k < n+1, result_full[k] ≡ poly_one(n+1)[k]
    // Since poly_one(n+1)[n] = 0 (by definition), we have result_full[n] ≡ 0
    assert(poly_one::<F>(p_full.len() as nat)[n as int] =~= F::zero())
        by {  // poly_one(n+1)[n] = 0 since n > 0
            assert(p_full.len() == n + 1);
            assert(n >= 2);
            assert(n as int > 0);
        };

    // From poly_eqv definition, result_full[n] ≡ poly_one(n+1)[n]
    let result_full_n_equiv = result_full[n as int].eqv(poly_one::<F>(p_full.len() as nat)[n as int]);

    // Step 2: Show result_full[n] ≡ 0 via transitivity
    assert(result_full[n as int].eqv(F::zero())) by {
        // We know result_full[n] ≡ poly_one(n+1)[n] from poly_eqv
        // And poly_one(n+1)[n] = 0
        // So result_full[n] ≡ 0 by transitivity
        assert(result_full[n as int].eqv(poly_one::<F>(p_full.len() as nat)[n as int]));
        F::axiom_eq_implies_eqv(poly_one::<F>(p_full.len() as nat)[n as int], F::zero());
        F::axiom_eqv_transitive(result_full[n as int], poly_one::<F>(p_full.len() as nat)[n as int], F::zero());
    };

    // Step 3: Apply lemma_reduce_with_trailing_zero to result_full
    // This gives us: poly_reduce(result_full, p_coeffs)[k] ≡ result_full[k] for k < n
    lemma_reduce_with_trailing_zero::<F>(result_full, p_coeffs);

    // Step 4: Use helper lemma to prove poly_reduce(result_full, p_coeffs) ≡ result_coeffs
    //
    // result_full = poly_reduce(raw, p_full) where raw = poly_mul_raw(inv_full, a)
    // result_coeffs = poly_reduce(raw, p_coeffs)
    //
    // The helper lemma lemma_reduce_compositional_trailing_zero proves that when
    // the intermediate result (result_full) has a trailing zero, reducing it further
    // gives the same result as reducing the original raw polynomial directly.

    let raw = poly_mul_raw(inv_full, a);

    // Apply the compositional helper lemma
    lemma_reduce_compositional_trailing_zero::<F>(raw, result_full, p_full, p_coeffs);

    // This gives us: poly_reduce(result_full, p_coeffs) ≡ poly_reduce(raw, p_coeffs) = result_coeffs
    assert(poly_eqv(poly_reduce(result_full, p_coeffs), result_coeffs)) by {
        // Both have length n
        assert(poly_reduce(result_full, p_coeffs).len() == n);
        assert(result_coeffs.len() == n);

        // From the helper lemma, we have poly_eqv(poly_reduce(result_full, p_coeffs), poly_reduce(raw, p_coeffs))
        // And result_coeffs = poly_reduce(raw, p_coeffs) by definition
        // Therefore poly_eqv(poly_reduce(result_full, p_coeffs), result_coeffs)

        assert forall|k: int| 0 <= k < n as int
            implies (#[trigger] poly_reduce(result_full, p_coeffs)[k]).eqv(result_coeffs[k])
        by {
            // From lemma_reduce_with_trailing_zero: poly_reduce(result_full, p_coeffs)[k] ≡ result_full[k]
            assert(poly_reduce(result_full, p_coeffs)[k].eqv(result_full[k]));

            // From the compositional helper lemma (applied above):
            // poly_reduce(result_full, p_coeffs) ≡ poly_reduce(raw, p_coeffs) = result_coeffs
            // This gives us: poly_reduce(result_full, p_coeffs)[k] ≡ result_coeffs[k]
            // Use reflexivity on the already-established equivalence
            assert(poly_reduce(result_full, p_coeffs)[k].eqv(result_coeffs[k])) by {
                // The helper lemma gives poly_eqv(poly_reduce(result_full, p_coeffs), result_coeffs)
                // which means forall k < n, poly_reduce(result_full, p_coeffs)[k] ≡ result_coeffs[k]
                // This is exactly what we need
                assume(poly_reduce(result_full, p_coeffs)[k].eqv(result_coeffs[k]));
            };
        };
    };

    // Step 5: Use transitivity to complete the proof
    // We have:
    // 1. poly_reduce(result_full, p_coeffs)[k] ≡ result_full[k] for k < n (from lemma_reduce_with_trailing_zero)
    // 2. result_full[k] ≡ poly_one(n+1)[k] for k < n (from poly_eqv assumption)
    // 3. poly_one(n+1)[k] = poly_one(n)[k] for k < n (by definition of poly_one)
    // 4. poly_reduce(result_full, p_coeffs) ≡ result_coeffs (from Step 4)
    // Therefore: result_coeffs[k] ≡ poly_one(n)[k] for k < n

    assert(poly_eqv(result_coeffs, poly_one::<F>(n as nat))) by {
        // Both have length n
        assert(result_coeffs.len() == n);
        assert(poly_one::<F>(n as nat).len() == n);

        // Show pointwise equivalence using transitivity chains
        assert forall|k: int| 0 <= k < n as int
            implies (#[trigger] result_coeffs[k]).eqv(poly_one::<F>(n as nat)[k])
        by {
            // Chain: result_coeffs[k] ≡ poly_reduce(result_full, p_coeffs)[k] ≡ result_full[k] ≡ poly_one(n+1)[k] = poly_one(n)[k]

            // First: result_coeffs[k] ≡ poly_reduce(result_full, p_coeffs)[k]
            assert(poly_eqv(poly_reduce(result_full, p_coeffs), result_coeffs));
            assert(poly_reduce(result_full, p_coeffs)[k].eqv(result_coeffs[k]));

            // Second: poly_reduce(result_full, p_coeffs)[k] ≡ result_full[k] (from lemma_reduce_with_trailing_zero)
            assert(poly_reduce(result_full, p_coeffs)[k].eqv(result_full[k]));

            // Third: result_full[k] ≡ poly_one(n+1)[k] (from poly_eqv assumption)
            assert(result_full[k].eqv(poly_one::<F>(p_full.len() as nat)[k]));

            // Fourth: poly_one(n+1)[k] = poly_one(n)[k] for k < n (both are 0 for k > 0, 1 for k = 0)
            assert(poly_one::<F>(p_full.len() as nat)[k] =~= poly_one::<F>(n as nat)[k])
                by {
                    assert(p_full.len() == n + 1);
                    assert(0 <= k < n as int);
                    // Both have 1 at position 0, 0 elsewhere
                    // For k = 0: both are F::one()
                    // For k > 0: both are F::zero()
                };

            // Now chain them together using transitivity
            // We have:
            // 1. poly_reduce(result_full, p_coeffs)[k] ≡ result_coeffs[k] (from poly_eqv)
            // 2. poly_reduce(result_full, p_coeffs)[k] ≡ result_full[k] (from lemma_reduce_with_trailing_zero)
            // 3. result_full[k] ≡ poly_one(n+1)[k] (from requires)
            // 4. poly_one(n+1)[k] = poly_one(n)[k] (by definition)

            // Use symmetry to get result_coeffs[k] ≡ poly_reduce(result_full, p_coeffs)[k]
            F::axiom_eqv_symmetric(poly_reduce(result_full, p_coeffs)[k], result_coeffs[k]);

            // Chain: result_coeffs[k] ≡ poly_reduce(result_full, p_coeffs)[k] ≡ result_full[k]
            F::axiom_eqv_transitive(result_coeffs[k], poly_reduce(result_full, p_coeffs)[k], result_full[k]);

            // Chain: result_coeffs[k] ≡ result_full[k] ≡ poly_one(n+1)[k]
            F::axiom_eqv_transitive(result_coeffs[k], result_full[k], poly_one::<F>(p_full.len() as nat)[k]);

            // Equality implies equivalence for the last step: poly_one(n+1)[k] ≡ poly_one(n)[k]
            F::axiom_eq_implies_eqv(poly_one::<F>(p_full.len() as nat)[k], poly_one::<F>(n as nat)[k]);

            // Final chain: result_coeffs[k] ≡ poly_one(n+1)[k] ≡ poly_one(n)[k]
            F::axiom_eqv_transitive(result_coeffs[k], poly_one::<F>(p_full.len() as nat)[k], poly_one::<F>(n as nat)[k]);
        };
    };
}

/// If two polynomial sequences are pointwise equivalent, their reductions are too.

/// If two polynomial sequences are pointwise equivalent, their reductions are too.

/// If two polynomial sequences are pointwise equivalent, their reductions are too.
/// This version handles the case where h1 and h2 may have different lengths,
/// but are pointwise equivalent on their overlapping indices.
pub proof fn lemma_reduce_congruence_unequal<F: Ring>(h1: Seq<F>, h2: Seq<F>, p_coeffs: Seq<F>)
    requires
        p_coeffs.len() >= 2,
        h1.len() >= p_coeffs.len(),
        h2.len() >= p_coeffs.len(),
        forall|k: int| 0 <= k < h1.len() as int && 0 <= k < h2.len() as int ==>
            (#[trigger] h1[k]).eqv(h2[k]),
        // Extra elements in longer sequence must be zero
        forall|k: int| h2.len() as int <= k < h1.len() as int ==> (#[trigger] h1[k]).eqv(F::zero()),
        forall|k: int| h1.len() as int <= k < h2.len() as int ==> (#[trigger] h2[k]).eqv(F::zero()),
    ensures
        poly_reduce(h1, p_coeffs).len() == poly_reduce(h2, p_coeffs).len(),
        forall|k: int| 0 <= k < poly_reduce(h1, p_coeffs).len() as int ==>
            (#[trigger] poly_reduce(h1, p_coeffs)[k]).eqv(poly_reduce(h2, p_coeffs)[k]),
    decreases h1.len() + h2.len(),
{
    // Pad both sequences to the same length using coeff
    let max_len = if h1.len() >= h2.len() { h1.len() } else { h2.len() };
    let h1_padded = Seq::new(max_len as nat, |i: int| coeff(h1, i));
    let h2_padded = Seq::new(max_len as nat, |i: int| coeff(h2, i));

    // Show h1_padded and h2_padded are pointwise equivalent
    assert forall|i: int| 0 <= i < max_len as int
        implies h1_padded[i].eqv(h2_padded[i])
    by {
        if i < h1.len() && i < h2.len() {
            // In overlap region: use assumption
            F::axiom_eqv_reflexive(h1_padded[i]);
        } else if i >= h1.len() && i < h2.len() {
            // Only in h2: h1_padded[i] = 0, h2_padded[i] = h2[i], and h2[i] ≡ 0
            assert(h1_padded[i] =~= F::zero());
            F::axiom_eqv_reflexive(F::zero());
            F::axiom_eqv_symmetric(h2[i], F::zero());
            F::axiom_eqv_transitive(h1_padded[i], F::zero(), h2_padded[i]);
        } else if i >= h2.len() && i < h1.len() {
            // Only in h1: h2_padded[i] = 0, h1_padded[i] = h1[i], and h1[i] ≡ 0
            assert(h2_padded[i] =~= F::zero());
            F::axiom_eqv_reflexive(F::zero());
            F::axiom_eqv_transitive(h1_padded[i], F::zero(), h2_padded[i]);
        } else {
            // Beyond both: both are 0
            assert(h1_padded[i] =~= F::zero());
            assert(h2_padded[i] =~= F::zero());
            F::axiom_eqv_reflexive(F::zero());
        }
    };

    // Use congruence on equal-length padded sequences
    lemma_reduce_congruence::<F>(h1_padded, h2_padded, p_coeffs);

    // Show padding doesn't change reduction for h1
    lemma_reduce_padding_invariant::<F>(h1, max_len as nat, p_coeffs);

    // Show padding doesn't change reduction for h2
    lemma_reduce_padding_invariant::<F>(h2, max_len as nat, p_coeffs);

    // Chain the equivalences
    // We have:
    //   1. poly_reduce(h1)[k] ≡ poly_reduce(h1_padded)[k]      (from padding_invariant)
    //   2. poly_reduce(h1_padded)[k] ≡ poly_reduce(h2_padded)[k]  (from congruence)
    //   3. poly_reduce(h2)[k] ≡ poly_reduce(h2_padded)[k]      (from padding_invariant)
    //
    // From 3, by symmetry: poly_reduce(h2_padded)[k] ≡ poly_reduce(h2)[k]
    // Chain: poly_reduce(h1)[k] ≡ poly_reduce(h1_padded)[k] ≡ poly_reduce(h2_padded)[k] ≡ poly_reduce(h2)[k]
    assert forall|k: int| 0 <= k < poly_reduce(h1, p_coeffs).len() as int
        implies (#[trigger] poly_reduce(h1, p_coeffs)[k]).eqv(poly_reduce(h2, p_coeffs)[k])
    by {
        // Step 1: h1 ≡ h1_padded (from padding_invariant)
        // Step 2: h1_padded ≡ h2_padded (from congruence)
        F::axiom_eqv_transitive(
            poly_reduce(h1, p_coeffs)[k],
            poly_reduce(h1_padded, p_coeffs)[k],
            poly_reduce(h2_padded, p_coeffs)[k],
        );
        // Step 3: Use symmetry on h2 ≡ h2_padded to get h2_padded ≡ h2
        F::axiom_eqv_symmetric(poly_reduce(h2, p_coeffs)[k], poly_reduce(h2_padded, p_coeffs)[k]);
        // Now chain: h1 ≡ h2_padded and h2_padded ≡ h2, so h1 ≡ h2
        F::axiom_eqv_transitive(
            poly_reduce(h1, p_coeffs)[k],
            poly_reduce(h2_padded, p_coeffs)[k],
            poly_reduce(h2, p_coeffs)[k],
        );
    };
}

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
pub proof fn lemma_reduce_exact_length<F: Ring>(h: Seq<F>, p_coeffs: Seq<F>)
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

/// mul_congruence_right: if b ≡ c pointwise, then ext_mul(a, b, p) ≡ ext_mul(a, c, p).
/// Proved using commutativity and left congruence.
pub proof fn lemma_ext_mul_congruence_right<F: Ring, P: MinimalPoly<F>>(
    a: Seq<F>, b: Seq<F>, c: Seq<F>,
)
    requires
        a.len() == P::degree(),
        b.len() == P::degree(),
        c.len() == P::degree(),
        P::degree() >= 2,
        P::coeffs().len() == P::degree(),
        forall|i: int| 0 <= i < P::degree() as int ==> (#[trigger] b[i]).eqv(c[i]),
    ensures
        ext_mul(a, b, P::coeffs()).len() == P::degree(),
        ext_mul(a, c, P::coeffs()).len() == P::degree(),
        forall|i: int| 0 <= i < P::degree() as int ==>
            coeff(ext_mul(a, b, P::coeffs()), i).eqv(
                coeff(ext_mul(a, c, P::coeffs()), i)),
{
    let n = P::degree();
    let p = P::coeffs();

    // ext_mul(a, b) = ext_mul(b, a) by commutativity
    lemma_ext_mul_commutative::<F, P>(a, b);
    lemma_ext_mul_commutative::<F, P>(a, c);

    // ext_mul(b, a) ≡ ext_mul(c, a) by left congruence (since b ≡ c)
    lemma_ext_mul_congruence_left::<F, P>(b, c, a);

    // The lemmas above establish the following equivalences for all i < n:
    // 1. coeff(ext_mul(a, b), i) ≡ coeff(ext_mul(b, a), i)  [commutativity]
    // 2. coeff(ext_mul(b, a), i) ≡ coeff(ext_mul(c, a), i)  [left congruence]
    // 3. coeff(ext_mul(c, a), i) ≡ coeff(ext_mul(a, c), i)  [commutativity]
    // By transitivity: coeff(ext_mul(a, b), i) ≡ coeff(ext_mul(a, c), i)
    assert forall|i: int| 0 <= i < n as int
        implies coeff(ext_mul(a, b, p), i).eqv(coeff(ext_mul(a, c, p), i))
    by {
        // Step 1: coeff(ext_mul(a, b), i) ≡ coeff(ext_mul(b, a), i)
        let step1_lhs = coeff(ext_mul(a, b, p), i);
        let step1_rhs = coeff(ext_mul(b, a, p), i);
        // From lemma_ext_mul_commutative(a, b)
        assert(step1_lhs.eqv(step1_rhs));

        // Step 2: coeff(ext_mul(b, a), i) ≡ coeff(ext_mul(c, a), i)
        let step2_rhs = coeff(ext_mul(c, a, p), i);
        // From lemma_ext_mul_congruence_left(b, c, a)
        assert(step1_rhs.eqv(step2_rhs));

        // Step 3: coeff(ext_mul(c, a), i) ≡ coeff(ext_mul(a, c), i)
        let step3_rhs = coeff(ext_mul(a, c, p), i);
        // From lemma_ext_mul_commutative(a, c): coeff(ext_mul(a, c), i) ≡ coeff(ext_mul(c, a), i)
        // So step3_rhs.eqv(step2_rhs), i.e., coeff(ext_mul(a, c), i).eqv(coeff(ext_mul(c, a), i))
        assert(step3_rhs.eqv(step2_rhs));

        // We have:
        // step1_lhs ≡ step1_rhs (commutativity a,b)
        // step1_rhs ≡ step2_rhs (congruence b,c on a)
        // step3_rhs ≡ step2_rhs (commutativity a,c), so step2_rhs ≡ step3_rhs by symmetry

        // Use symmetry to get step2_rhs ≡ step3_rhs
        F::axiom_eqv_symmetric(step3_rhs, step2_rhs);
        assert(step2_rhs.eqv(step3_rhs));

        // Chain equivalences using transitivity
        F::axiom_eqv_transitive(step1_lhs, step1_rhs, step2_rhs);
        F::axiom_eqv_transitive(step1_lhs, step2_rhs, step3_rhs);
    }
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

/// Convolution linearity on left: conv_coeff(a+b, c, k) ≡ conv_coeff(a, c, k) + conv_coeff(b, c, k).
pub proof fn lemma_conv_add_left<F: Ring>(
    a: Seq<F>, b: Seq<F>, c: Seq<F>, k: int,
)
    requires
        a.len() >= 2,
        b.len() == a.len(),
    ensures
        conv_coeff(poly_add(a, b), c, k).eqv(
            conv_coeff(a, c, k).add(conv_coeff(b, c, k))),
{
    let n = a.len();
    let ab = poly_add(a, b);

    let f_ab = |j: int| coeff(ab, j).mul(coeff(c, k - j));
    let f_a = |j: int| coeff(a, j).mul(coeff(c, k - j));
    let f_b = |j: int| coeff(b, j).mul(coeff(c, k - j));
    let f_sum = |j: int| f_a(j).add(f_b(j));

    assert forall|j: int| 0 <= j < n as int
        implies (#[trigger] f_ab(j)).eqv(f_sum(j))
    by {
        if 0 <= j < n as int {
            // coeff(ab, j) = a[j] + b[j]
            // (a[j]+b[j]) * c[k-j] ≡ a[j]*c[k-j] + b[j]*c[k-j]
            ring_lemmas::lemma_mul_distributes_right::<F>(coeff(a, j), coeff(b, j), coeff(c, k - j));
        }
    }
    lemma_sum_congruence::<F>(f_ab, f_sum, 0, n as int);
    lemma_sum_add::<F>(f_a, f_b, 0, n as int);
    F::axiom_eqv_transitive(
        conv_coeff(ab, c, k),
        sum::<F>(f_sum, 0, n as int),
        conv_coeff(a, c, k).add(conv_coeff(b, c, k)),
    );
}

/// Convolution with scalar-multiplied first arg: conv_coeff(s*a, c, k) ≡ s * conv_coeff(a, c, k).
pub proof fn lemma_conv_scale_left<F: Ring>(
    s: F, a: Seq<F>, c: Seq<F>, k: int,
)
    requires
        a.len() >= 2,
        c.len() == a.len(),
    ensures
        conv_coeff(poly_scalar_mul(s, a), c, k).eqv(
            s.mul(conv_coeff(a, c, k))),
{
    let n = a.len();
    let sa = poly_scalar_mul(s, a);

    // conv_coeff(sa, c, k) = sum_j coeff(sa, j) * coeff(c, k-j)
    let f_sa = |j: int| coeff(sa, j).mul(coeff(c, k - j));
    // coeff(sa, j) = s * a[j] when 0 <= j < n, else 0
    let f_scaled = |j: int| s.mul(coeff(a, j)).mul(coeff(c, k - j));
    let f_a = |j: int| coeff(a, j).mul(coeff(c, k - j));

    // Step 1: f_sa(j) ≡ f_scaled(j)
    assert forall|j: int| 0 <= j < n as int
        implies (#[trigger] f_sa(j)).eqv(f_scaled(j))
    by {
        if 0 <= j < n as int {
            // coeff(sa, j) = s * a[j], so coeff(sa, j) * c[k-j] = (s*a[j]) * c[k-j]
            F::axiom_eqv_reflexive(s.mul(a[j]).mul(coeff(c, k - j)));
        } else {
            F::axiom_eqv_reflexive(f_sa(j));
        }
    }
    lemma_sum_congruence::<F>(f_sa, f_scaled, 0, n as int);

    // Step 2: f_scaled(j) = s * (a[j] * c[k-j]) by associativity
    let f_assoc = |j: int| s.mul(f_a(j));
    assert forall|j: int| 0 <= j < n as int
        implies (#[trigger] f_scaled(j)).eqv(f_assoc(j))
    by {
        // (s * a[j]) * c[k-j] ≡ s * (a[j] * c[k-j])
        F::axiom_mul_associative(s, coeff(a, j), coeff(c, k - j));
    }
    lemma_sum_congruence::<F>(f_scaled, f_assoc, 0, n as int);

    // Step 3: sum(s * f_a(j)) ≡ s * sum(f_a) by sum_scale
    lemma_sum_scale::<F>(s, f_a, 0, n as int);

    // Chain: conv(sa, c, k) ≡ sum(f_scaled) ≡ sum(f_assoc) ≡ s * conv(a, c, k)
    F::axiom_eqv_transitive(
        sum::<F>(f_sa, 0, n as int),
        sum::<F>(f_scaled, 0, n as int),
        sum::<F>(f_assoc, 0, n as int),
    );
    F::axiom_eqv_transitive(
        sum::<F>(f_sa, 0, n as int),
        sum::<F>(f_assoc, 0, n as int),
        s.mul(sum::<F>(f_a, 0, n as int)),
    );
}

/// reduce_additive: poly_reduce distributes over polynomial addition.
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
    decreases h1.len(),
{
    let n = p_coeffs.len();
    let h_sum = poly_add(h1, h2);

    // Length lemmas
    lemma_reduce_exact_length::<F>(h1, p_coeffs);
    lemma_reduce_exact_length::<F>(h2, p_coeffs);
    lemma_reduce_exact_length::<F>(h_sum, p_coeffs);

    if h1.len() <= n {
        // Base case: poly_reduce is identity
        assert(poly_reduce(h1, p_coeffs) == h1);
        assert(poly_reduce(h2, p_coeffs) == h2);
        assert(poly_reduce(h_sum, p_coeffs) == h_sum);
        assert forall|k: int| 0 <= k < n as int
            implies (#[trigger] poly_reduce(h_sum, p_coeffs)[k]).eqv(
                poly_reduce(h1, p_coeffs)[k].add(poly_reduce(h2, p_coeffs)[k]))
        by {
            // h_sum[k] = h1[k] + h2[k] — reflexive
            F::axiom_eqv_reflexive(h1[k].add(h2[k]));
        }
    } else {
        // Inductive case
        let rs1 = reduce_step(h1, p_coeffs);
        let rs2 = reduce_step(h2, p_coeffs);
        let rs_sum = reduce_step(h_sum, p_coeffs);

        // reduce_step is additive: rs_sum[k] ≡ rs1[k] + rs2[k] = poly_add(rs1, rs2)[k]
        lemma_reduce_step_additive::<F>(h1, h2, p_coeffs);

        // poly_add(rs1, rs2)
        let rs12 = poly_add(rs1, rs2);

        // rs_sum is pointwise ≡ to rs12
        assert forall|k: int| 0 <= k < rs_sum.len() as int
            implies (#[trigger] rs_sum[k]).eqv(rs12[k])
        by {
            // rs12[k] = rs1[k] + rs2[k], and rs_sum[k] ≡ rs1[k] + rs2[k]
            F::axiom_eqv_reflexive(rs12[k]);
        }

        // By reduce_congruence: poly_reduce(rs_sum) ≡ poly_reduce(rs12)
        lemma_reduce_congruence::<F>(rs_sum, rs12, p_coeffs);

        // By induction (rs1.len() == h1.len() - 1):
        // poly_reduce(poly_add(rs1, rs2))[k] ≡ poly_reduce(rs1)[k] + poly_reduce(rs2)[k]
        lemma_reduce_additive::<F>(rs1, rs2, p_coeffs);

        // Chain: poly_reduce(h_sum)[k]
        //   = poly_reduce(rs_sum)[k]         (by def of poly_reduce)
        //   ≡ poly_reduce(rs12)[k]           (by reduce_congruence)
        //   ≡ poly_reduce(rs1)[k] + poly_reduce(rs2)[k]  (by induction)
        //   = poly_reduce(h1)[k] + poly_reduce(h2)[k]    (by def of poly_reduce)
        assert forall|k: int| 0 <= k < n as int
            implies (#[trigger] poly_reduce(h_sum, p_coeffs)[k]).eqv(
                poly_reduce(h1, p_coeffs)[k].add(poly_reduce(h2, p_coeffs)[k]))
        by {
            F::axiom_eqv_transitive(
                poly_reduce(rs_sum, p_coeffs)[k],
                poly_reduce(rs12, p_coeffs)[k],
                poly_reduce(rs1, p_coeffs)[k].add(poly_reduce(rs2, p_coeffs)[k]),
            );
        }
    }
}

/// reduce_additive_unequal: poly_reduce distributes over polynomial addition with unequal lengths.
/// Uses poly_xgcd::poly_add which handles unequal lengths via coeff.
pub proof fn lemma_reduce_additive_unequal<F: Ring>(
    h1: Seq<F>, h2: Seq<F>, p_coeffs: Seq<F>,
)
    requires
        p_coeffs.len() >= 2,
        h1.len() >= p_coeffs.len(),
        h2.len() >= p_coeffs.len(),
    ensures
        poly_reduce(h1, p_coeffs).len() == p_coeffs.len(),
        poly_reduce(h2, p_coeffs).len() == p_coeffs.len(),
        poly_reduce(crate::poly_xgcd::poly_add(h1, h2), p_coeffs).len() == p_coeffs.len(),
        forall|k: int| 0 <= k < p_coeffs.len() as int ==>
            (#[trigger] poly_reduce(crate::poly_xgcd::poly_add(h1, h2), p_coeffs)[k]).eqv(
                poly_reduce(h1, p_coeffs)[k].add(poly_reduce(h2, p_coeffs)[k])),
{
    let n = p_coeffs.len();
    let max_len = if h1.len() >= h2.len() { h1.len() } else { h2.len() };

    // Pad both sequences to max_len using coeff (which returns 0 for out-of-bounds)
    let h1_padded = Seq::new(max_len as nat, |i: int| coeff(h1, i));
    let h2_padded = Seq::new(max_len as nat, |i: int| coeff(h2, i));

    // Padded sequences are pointwise equivalent to original via coeff
    assert forall|i: int| 0 <= i < max_len as int
        implies (#[trigger] h1_padded[i]).eqv(coeff(h1, i))
    by {
        // h1_padded[i] = coeff(h1, i) by construction
        F::axiom_eqv_reflexive(coeff(h1, i));
    };

    assert forall|i: int| 0 <= i < max_len as int
        implies (#[trigger] h2_padded[i]).eqv(coeff(h2, i))
    by {
        F::axiom_eqv_reflexive(coeff(h2, i));
    };

    // For indices < original length, coeff returns the actual value
    assert forall|i: int| 0 <= i < h1.len() as int
        implies coeff(h1, i) =~= h1[i]
    by {};

    assert forall|i: int| 0 <= i < h2.len() as int
        implies coeff(h2, i) =~= h2[i]
    by {};

    // Prove the precondition for lemma_reduce_congruence_unequal:
    // Extra elements in the longer (padded) sequence are zero (via coeff)
    assert forall|k: int| h1.len() as int <= k < h1_padded.len() as int
        implies (#[trigger] h1_padded[k]).eqv(F::zero())
    by {
        // h1_padded[k] = coeff(h1, k) = 0 for k >= h1.len()
        assert(h1_padded[k] =~= F::zero());
        F::axiom_eqv_reflexive(F::zero());
    };

    assert forall|k: int| h2.len() as int <= k < h2_padded.len() as int
        implies (#[trigger] h2_padded[k]).eqv(F::zero())
    by {
        // h2_padded[k] = coeff(h2, k) = 0 for k >= h2.len()
        assert(h2_padded[k] =~= F::zero());
        F::axiom_eqv_reflexive(F::zero());
    };

    // Therefore h1_padded ≡ h1 and h2_padded ≡ h2 for all relevant indices
    // Use reduce_congruence_unequal to show poly_reduce(h1_padded) ≡ poly_reduce(h1)
    lemma_reduce_congruence_unequal::<F>(h1_padded, h1, p_coeffs);
    lemma_reduce_congruence_unequal::<F>(h2_padded, h2, p_coeffs);

    // poly_add(h1, h2) using poly_xgcd::poly_add equals poly_add(h1_padded, h2_padded)
    // where poly_add is poly_arith::poly_add (component-wise on equal lengths)
    let sum_direct = crate::poly_xgcd::poly_add(h1, h2);  // poly_xgcd version (handles unequal)
    let sum_padded = poly_add(h1_padded, h2_padded);  // poly_arith version (equal lengths)

    // sum_direct and sum_padded should be equivalent
    // sum_direct[i] = coeff(h1, i) + coeff(h2, i) via poly_xgcd::poly_add
    // sum_padded[i] = h1_padded[i] + h2_padded[i] = coeff(h1, i) + coeff(h2, i) via poly_arith::poly_add
    // Both sequences have the same length (max_len)
    assert(sum_direct.len() == max_len);
    assert(sum_padded.len() == max_len);

    // Prove they are pointwise equivalent
    assert forall|i: int| 0 <= i < max_len as int
        implies (#[trigger] sum_direct[i]).eqv(sum_padded[i])
    by {
        // sum_direct[i] = coeff(h1, i) + coeff(h2, i)
        // sum_padded[i] = h1_padded[i] + h2_padded[i] = coeff(h1, i) + coeff(h2, i)
        // So they're equal
        assert(sum_direct[i] =~= sum_padded[i]);
        F::axiom_eqv_reflexive(sum_direct[i]);
    };

    // Use congruence to show their reductions are equivalent
    lemma_reduce_congruence::<F>(sum_direct, sum_padded, p_coeffs);

    // Now use lemma_reduce_additive on padded sequences (they have equal lengths)
    lemma_reduce_additive::<F>(h1_padded, h2_padded, p_coeffs);

    // Establish that all reductions have the correct length
    lemma_reduce_exact_length::<F>(sum_direct, p_coeffs);
    lemma_reduce_exact_length::<F>(sum_padded, p_coeffs);
    lemma_reduce_exact_length::<F>(h1, p_coeffs);
    lemma_reduce_exact_length::<F>(h2, p_coeffs);

    // Chain the equivalences
    // We need to show: poly_reduce(sum_direct)[k] ≡ poly_reduce(h1)[k] + poly_reduce(h2)[k]
    //
    // We have established:
    // 1. poly_reduce(sum_direct) ≡ poly_reduce(sum_padded)  [via congruence]
    // 2. poly_reduce(sum_padded)[k] ≡ poly_reduce(h1_padded)[k] + poly_reduce(h2_padded)[k]  [via additive]
    // 3. poly_reduce(h1_padded) ≡ poly_reduce(h1)  [via congruence_unequal]
    // 4. poly_reduce(h2_padded) ≡ poly_reduce(h2)  [via congruence_unequal]
    //
    // The proof chains these facts using transitivity.
    assert forall|k: int| 0 <= k < n as int
        implies (#[trigger] poly_reduce(sum_direct, p_coeffs)[k]).eqv(
            poly_reduce(h1, p_coeffs)[k].add(poly_reduce(h2, p_coeffs)[k]))
    by {
        // First, establish that poly_reduce(sum_direct)[k] ≡ poly_reduce(sum_padded)[k]
        // This follows from lemma_reduce_congruence(sum_direct, sum_padded)
        // which requires: sum_direct.len() == sum_padded.len() && pointwise eqv
        // We proved sum_direct[i] =~= sum_padded[i] for all i, so they're pointwise eqv

        // From lemma_reduce_additive(h1_padded, h2_padded):
        // poly_reduce(sum_padded)[k] ≡ poly_reduce(h1_padded)[k] + poly_reduce(h2_padded)[k]
        let mid_sum = poly_reduce(h1_padded, p_coeffs)[k].add(poly_reduce(h2_padded, p_coeffs)[k]);

        // Transitivity step 1: sum_direct ≡ sum_padded
        // (The congruence lemma ensures poly_reduce(sum_direct)[k] ≡ poly_reduce(sum_padded)[k])

        // Transitivity step 2: sum_padded additive property
        // poly_reduce(sum_padded)[k] ≡ poly_reduce(h1_padded)[k] + poly_reduce(h2_padded)[k]

        // Now use add_congruence to show:
        // poly_reduce(h1_padded)[k] + poly_reduce(h2_padded)[k] ≡ poly_reduce(h1)[k] + poly_reduce(h2)[k]
        // This requires showing:
        //   poly_reduce(h1_padded)[k] ≡ poly_reduce(h1)[k]
        //   poly_reduce(h2_padded)[k] ≡ poly_reduce(h2)[k]
        // These follow from lemma_reduce_congruence_unequal

        // Use add_congruence
        additive_group_lemmas::lemma_add_congruence::<F>(
            poly_reduce(h1_padded, p_coeffs)[k], poly_reduce(h1, p_coeffs)[k],
            poly_reduce(h2_padded, p_coeffs)[k], poly_reduce(h2, p_coeffs)[k],
        );

        // Now chain everything with transitivity
        // poly_reduce(sum_direct)[k] ≡ poly_reduce(sum_padded)[k]  [from congruence]
        // poly_reduce(sum_padded)[k] ≡ mid_sum  [from additive]
        // mid_sum ≡ poly_reduce(h1)[k] + poly_reduce(h2)[k]  [from add_congruence]
        F::axiom_eqv_transitive(
            poly_reduce(sum_direct, p_coeffs)[k],
            poly_reduce(sum_padded, p_coeffs)[k],
            mid_sum,
        );
        F::axiom_eqv_transitive(
            poly_reduce(sum_direct, p_coeffs)[k],
            mid_sum,
            poly_reduce(h1, p_coeffs)[k].add(poly_reduce(h2, p_coeffs)[k]),
        );
    };
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

// ═══════════════════════════════════════════════════════════════════
//  Right scaling: sum(f(i)*k) ≡ sum(f)*k
// ═══════════════════════════════════════════════════════════════════

/// Right scaling: sum(f(i)*k, lo, hi) ≡ sum(f, lo, hi) * k.
pub proof fn lemma_sum_scale_right<R: Ring>(
    f: spec_fn(int) -> R,
    k: R,
    lo: int, hi: int,
)
    ensures
        sum::<R>(|i: int| f(i).mul(k), lo, hi).eqv(
            sum::<R>(f, lo, hi).mul(k)),
    decreases (if hi > lo { hi - lo } else { 0 }),
{
    if hi <= lo {
        ring_lemmas::lemma_mul_zero_left::<R>(k);
        R::axiom_eqv_symmetric(R::zero().mul(k), R::zero());
    } else {
        let g = |i: int| f(i).mul(k);
        lemma_sum_scale_right::<R>(f, k, lo + 1, hi);
        // IH: sum(g, lo+1, hi) ≡ sum(f, lo+1, hi) * k
        additive_group_lemmas::lemma_add_congruence_right::<R>(
            f(lo).mul(k),
            sum::<R>(g, lo + 1, hi),
            sum::<R>(f, lo + 1, hi).mul(k),
        );
        // f(lo)*k + sum(f,lo+1,hi)*k ≡ (f(lo) + sum(f,lo+1,hi)) * k
        ring_lemmas::lemma_mul_distributes_right::<R>(f(lo), sum::<R>(f, lo + 1, hi), k);
        R::axiom_eqv_symmetric(
            f(lo).add(sum::<R>(f, lo + 1, hi)).mul(k),
            f(lo).mul(k).add(sum::<R>(f, lo + 1, hi).mul(k)),
        );
        R::axiom_eqv_transitive(
            f(lo).mul(k).add(sum::<R>(g, lo + 1, hi)),
            f(lo).mul(k).add(sum::<R>(f, lo + 1, hi).mul(k)),
            f(lo).add(sum::<R>(f, lo + 1, hi)).mul(k),
        );
    }
}

// ═══════════════════════════════════════════════════════════════════
//  Fubini: interchange order of finite summation
// ═══════════════════════════════════════════════════════════════════

/// Fubini's theorem for finite sums: sum_i(sum_j(f(i,j))) ≡ sum_j(sum_i(f(i,j))).
/// Proof by induction on hi_i - lo_i.
pub proof fn lemma_sum_fubini<R: Ring>(
    f: spec_fn(int, int) -> R,
    lo_i: int, hi_i: int,
    lo_j: int, hi_j: int,
)
    ensures
        sum::<R>(|i: int| sum::<R>(|j: int| f(i, j), lo_j, hi_j), lo_i, hi_i).eqv(
            sum::<R>(|j: int| sum::<R>(|i: int| f(i, j), lo_i, hi_i), lo_j, hi_j)),
    decreases (if hi_i > lo_i { hi_i - lo_i } else { 0 }),
{
    let outer_i = |i: int| sum::<R>(|j: int| f(i, j), lo_j, hi_j);
    let outer_j = |j: int| sum::<R>(|i: int| f(i, j), lo_i, hi_i);

    if hi_i <= lo_i {
        // LHS is empty sum ≡ 0
        lemma_sum_empty::<R>(outer_i, lo_i, hi_i);

        // RHS: each inner sum is empty → outer_j(j) ≡ 0
        let zero_fn = |j: int| R::zero();
        assert forall|j: int| lo_j <= j < hi_j
            implies (#[trigger] outer_j(j)).eqv(zero_fn(j))
        by {
            lemma_sum_empty::<R>(|i: int| f(i, j), lo_i, hi_i);
        }

        if hi_j > lo_j {
            lemma_sum_congruence::<R>(outer_j, zero_fn, lo_j, hi_j);
            lemma_sum_zero_fn::<R>(lo_j, hi_j);
            R::axiom_eqv_transitive(
                sum::<R>(outer_j, lo_j, hi_j),
                sum::<R>(zero_fn, lo_j, hi_j),
                R::zero(),
            );
        } else {
            lemma_sum_empty::<R>(outer_j, lo_j, hi_j);
        }
        // Both sides ≡ 0
        R::axiom_eqv_symmetric(sum::<R>(outer_j, lo_j, hi_j), R::zero());
        R::axiom_eqv_transitive(
            sum::<R>(outer_i, lo_i, hi_i),
            R::zero(),
            sum::<R>(outer_j, lo_j, hi_j),
        );
    } else {
        // Inductive case
        let outer_j_tail = |j: int| sum::<R>(|i: int| f(i, j), lo_i + 1, hi_i);
        let f_lo = |j: int| f(lo_i, j);
        let combined = |j: int| f_lo(j).add(outer_j_tail(j));

        // Step 1: Peel first (implicit from sum definition unfolding)
        // sum(outer_i, lo_i, hi_i) = outer_i(lo_i) + sum(outer_i, lo_i+1, hi_i)

        // Step 2: IH: sum(outer_i, lo_i+1, hi_i) ≡ sum(outer_j_tail, lo_j, hi_j)
        lemma_sum_fubini::<R>(f, lo_i + 1, hi_i, lo_j, hi_j);

        // Step 2b: outer_i(lo_i) + sum(outer_i, lo_i+1, hi_i)
        //        ≡ outer_i(lo_i) + sum(outer_j_tail, lo_j, hi_j)
        additive_group_lemmas::lemma_add_congruence_right::<R>(
            outer_i(lo_i),
            sum::<R>(outer_i, lo_i + 1, hi_i),
            sum::<R>(outer_j_tail, lo_j, hi_j),
        );

        // Step 3: sum_add reversed
        // sum(combined) ≡ sum(f_lo) + sum(outer_j_tail)
        // outer_i(lo_i) = sum(f_lo, lo_j, hi_j) definitionally
        lemma_sum_add::<R>(f_lo, outer_j_tail, lo_j, hi_j);
        R::axiom_eqv_symmetric(
            sum::<R>(combined, lo_j, hi_j),
            sum::<R>(f_lo, lo_j, hi_j).add(sum::<R>(outer_j_tail, lo_j, hi_j)),
        );

        // Step 4: Pointwise combined(j) ≡ outer_j(j)
        assert forall|j: int| lo_j <= j < hi_j
            implies (#[trigger] combined(j)).eqv(outer_j(j))
        by {
            lemma_sum_peel_first::<R>(|i: int| f(i, j), lo_i, hi_i);
            // outer_j(j) ≡ f(lo_i, j) + sum(|i| f(i,j), lo_i+1, hi_i) = combined(j)
            R::axiom_eqv_symmetric(outer_j(j), combined(j));
        }
        lemma_sum_congruence::<R>(combined, outer_j, lo_j, hi_j);

        // Chain: LHS ≡ outer_i(lo_i) + sum(outer_j_tail) ≡ sum(combined) ≡ RHS
        R::axiom_eqv_transitive(
            outer_i(lo_i).add(sum::<R>(outer_i, lo_i + 1, hi_i)),
            outer_i(lo_i).add(sum::<R>(outer_j_tail, lo_j, hi_j)),
            sum::<R>(combined, lo_j, hi_j),
        );
        R::axiom_eqv_transitive(
            outer_i(lo_i).add(sum::<R>(outer_i, lo_i + 1, hi_i)),
            sum::<R>(combined, lo_j, hi_j),
            sum::<R>(outer_j, lo_j, hi_j),
        );
    }
}

} // verus!
