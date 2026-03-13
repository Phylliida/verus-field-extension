use verus_algebra::summation::sum;
use verus_algebra::traits::additive_commutative_monoid::AdditiveCommutativeMonoid;
use verus_algebra::traits::additive_group::AdditiveGroup;
use verus_algebra::traits::equivalence::Equivalence;
use verus_algebra::traits::ring::Ring;
use vstd::prelude::*;

verus! {

// ═══════════════════════════════════════════════════════════════════
//  Coefficient access
// ═══════════════════════════════════════════════════════════════════

/// Safe coefficient access: returns F::zero() for out-of-bounds indices.
pub open spec fn coeff<F: Ring>(f: Seq<F>, k: int) -> F {
    if 0 <= k < f.len() as int {
        f[k]
    } else {
        F::zero()
    }
}

// ═══════════════════════════════════════════════════════════════════
//  Component-wise polynomial operations (all length n)
// ═══════════════════════════════════════════════════════════════════

/// Zero polynomial of length n: [0, 0, ..., 0].
pub open spec fn poly_zero<F: Ring>(n: nat) -> Seq<F> {
    Seq::new(n as nat, |_i: int| F::zero())
}

/// One polynomial of length n (n ≥ 1): [1, 0, 0, ..., 0].
pub open spec fn poly_one<F: Ring>(n: nat) -> Seq<F>
    recommends n >= 1
{
    Seq::new(n as nat, |i: int| if i == 0 { F::one() } else { F::zero() })
}

/// Component-wise addition. Requires same length.
pub open spec fn poly_add<F: Ring>(a: Seq<F>, b: Seq<F>) -> Seq<F>
    recommends a.len() == b.len()
{
    Seq::new(a.len(), |i: int| a[i].add(b[i]))
}

/// Component-wise negation.
pub open spec fn poly_neg<F: Ring>(a: Seq<F>) -> Seq<F> {
    Seq::new(a.len(), |i: int| a[i].neg())
}

/// Component-wise subtraction. Requires same length.
pub open spec fn poly_sub<F: Ring>(a: Seq<F>, b: Seq<F>) -> Seq<F>
    recommends a.len() == b.len()
{
    Seq::new(a.len(), |i: int| a[i].sub(b[i]))
}

/// Component-wise equivalence.
pub open spec fn poly_eqv<F: Ring>(a: Seq<F>, b: Seq<F>) -> bool
    recommends a.len() == b.len()
{
    a.len() == b.len() && forall|i: int| 0 <= i < a.len() as int ==> (#[trigger] a[i]).eqv(b[i])
}

// ═══════════════════════════════════════════════════════════════════
//  Convolution (polynomial multiplication before reduction)
// ═══════════════════════════════════════════════════════════════════

/// k-th convolution coefficient: sum_{j=0}^{len(a)-1} a[j] * b[k-j].
/// Uses `coeff` for safe access so b[k-j] = 0 when out of range.
pub open spec fn conv_coeff<F: Ring>(a: Seq<F>, b: Seq<F>, k: int) -> F {
    sum::<F>(|j: int| coeff(a, j).mul(coeff(b, k - j)), 0, a.len() as int)
}

/// Full convolution product. Length = len(a) + len(b) - 1 when both nonempty.
pub open spec fn poly_mul_raw<F: Ring>(a: Seq<F>, b: Seq<F>) -> Seq<F>
    recommends a.len() > 0 && b.len() > 0
{
    let out_len = (a.len() + b.len() - 1) as nat;
    Seq::new(out_len, |k: int| conv_coeff(a, b, k))
}

// ═══════════════════════════════════════════════════════════════════
//  Polynomial reduction modulo a monic polynomial
// ═══════════════════════════════════════════════════════════════════

/// One step of polynomial long division by a monic polynomial p(x) = x^n + p_coeffs.
///
/// Given h of degree m ≥ n (i.e., h.len() > p_coeffs.len()), subtract
/// h[m-1] · x^{m-1-n} · p(x) to cancel the leading term. Since p is monic,
/// this reduces h.len() by 1.
///
/// Result has length h.len() - 1.
pub open spec fn reduce_step<F: Ring>(h: Seq<F>, p_coeffs: Seq<F>) -> Seq<F>
    recommends
        h.len() > p_coeffs.len(),
        p_coeffs.len() >= 2,
{
    let n = p_coeffs.len();
    let m = h.len();
    let lead = h[m - 1];       // leading coefficient of h
    let shift = m - 1 - n;     // degree shift: x^shift · p(x)
    // h_k - lead * p_coeffs[k - shift]  for 0 ≤ k < m - 1
    // (The x^m-1 term is implicitly cancelled by the monic leading term.)
    Seq::new((m - 1) as nat, |k: int|
        if shift as int <= k < shift + n as int {
            h[k].sub(lead.mul(p_coeffs[k - shift]))
        } else {
            h[k]
        }
    )
}

/// Repeatedly apply reduce_step until degree < n (i.e., len ≤ p_coeffs.len()).
pub open spec fn poly_reduce<F: Ring>(h: Seq<F>, p_coeffs: Seq<F>) -> Seq<F>
    recommends p_coeffs.len() >= 2
    decreases h.len()
{
    if h.len() <= p_coeffs.len() {
        h
    } else {
        poly_reduce(reduce_step(h, p_coeffs), p_coeffs)
    }
}

/// Multiplication in F[x]/(p(x)): convolve then reduce.
pub open spec fn ext_mul<F: Ring>(a: Seq<F>, b: Seq<F>, p_coeffs: Seq<F>) -> Seq<F>
    recommends
        a.len() == p_coeffs.len(),
        b.len() == p_coeffs.len(),
        p_coeffs.len() >= 2,
{
    poly_reduce(poly_mul_raw(a, b), p_coeffs)
}

// ═══════════════════════════════════════════════════════════════════
//  Additional polynomial operations for associativity proof
// ═══════════════════════════════════════════════════════════════════

/// The full monic polynomial p(x) = x^n + p_coeffs as a sequence of length n+1.
/// p_full_seq([c_0, ..., c_{n-1}]) = [c_0, ..., c_{n-1}, 1].
pub open spec fn p_full_seq<F: Ring>(p_coeffs: Seq<F>) -> Seq<F> {
    Seq::new((p_coeffs.len() + 1) as nat, |i: int|
        if i < p_coeffs.len() as int { p_coeffs[i] } else { F::one() })
}

/// Scalar multiplication of a polynomial: s * [a_0, ..., a_{n-1}] = [s*a_0, ..., s*a_{n-1}].
pub open spec fn poly_scalar_mul<F: Ring>(s: F, p: Seq<F>) -> Seq<F> {
    Seq::new(p.len(), |i: int| s.mul(p[i]))
}

/// Shift polynomial by prepending zeros: poly_shift(p, k) has length p.len()+k,
/// with zeros at indices [0, k) and p[i-k] at indices [k, k+p.len()).
pub open spec fn poly_shift<F: Ring>(p: Seq<F>, shift: nat) -> Seq<F> {
    Seq::new((p.len() + shift) as nat, |i: int|
        if i < shift as int { F::zero() } else { p[i - shift] })
}

/// Standard basis vector e_j of length n: all zeros except 1 at position j.
pub open spec fn poly_basis<F: Ring>(n: nat, j: int) -> Seq<F>
    recommends 0 <= j < n as int
{
    Seq::new(n, |i: int| if i == j { F::one() } else { F::zero() })
}

} // verus!
