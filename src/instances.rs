use vstd::prelude::*;
use verus_algebra::traits::equivalence::Equivalence;
use verus_algebra::traits::ring::Ring;
use verus_rational::rational::Rational;
use crate::minimal_poly::MinimalPoly;
use crate::spec::*;

verus! {

// ═══════════════════════════════════════════════════════════════════
//  Cube root of 2: p(x) = x³ - 2
// ═══════════════════════════════════════════════════════════════════
//
// Elements of ℚ(∛2) are polynomials a + b·∛2 + c·(∛2)² with a,b,c ∈ ℚ.
// Minimal polynomial: x³ - 2, coefficients [-2, 0, 0], degree 3.

/// Minimal polynomial for ∛2: p(x) = x³ - 2.
pub struct CubeRoot2;

impl MinimalPoly<Rational> for CubeRoot2 {
    open spec fn degree() -> nat { 3 }

    open spec fn coeffs() -> Seq<Rational> {
        seq![
            Rational::from_int_spec(-2),  // c_0 = -2
            Rational::from_int_spec(0),   // c_1 = 0
            Rational::from_int_spec(0),   // c_2 = 0
        ]
        // p(x) = x³ + 0·x² + 0·x + (-2) = x³ - 2
    }

    proof fn axiom_degree_ge_2() { }

    proof fn axiom_coeffs_len() { }
}

/// Type alias for ℚ(∛2).
pub type QCubeRoot2 = SpecFieldExt<Rational, CubeRoot2>;

// ═══════════════════════════════════════════════════════════════════
//  Fifth root of 2: p(x) = x⁵ - 2
// ═══════════════════════════════════════════════════════════════════
//
// Elements of ℚ(⁵√2) are polynomials a₀ + a₁·α + a₂·α² + a₃·α³ + a₄·α⁴
// where α = ⁵√2.

/// Minimal polynomial for ⁵√2: p(x) = x⁵ - 2.
pub struct FifthRoot2;

impl MinimalPoly<Rational> for FifthRoot2 {
    open spec fn degree() -> nat { 5 }

    open spec fn coeffs() -> Seq<Rational> {
        seq![
            Rational::from_int_spec(-2),  // c_0 = -2
            Rational::from_int_spec(0),   // c_1 = 0
            Rational::from_int_spec(0),   // c_2 = 0
            Rational::from_int_spec(0),   // c_3 = 0
            Rational::from_int_spec(0),   // c_4 = 0
        ]
        // p(x) = x⁵ + 0·x⁴ + 0·x³ + 0·x² + 0·x + (-2) = x⁵ - 2
    }

    proof fn axiom_degree_ge_2() { }

    proof fn axiom_coeffs_len() { }
}

/// Type alias for ℚ(⁵√2).
pub type QFifthRoot2 = SpecFieldExt<Rational, FifthRoot2>;

// ═══════════════════════════════════════════════════════════════════
//  Primitive cube root of unity: p(x) = x² + x + 1
// ═══════════════════════════════════════════════════════════════════
//
// The cyclotomic polynomial Φ₃(x) = x² + x + 1 has roots ω = e^{2πi/3}
// and ω² = e^{4πi/3}. Over ℚ, this is irreducible (Eisenstein at p=3
// after substituting x = y+1 doesn't quite work, but irreducibility
// follows from Φ₃ having no rational roots since ω is complex).
//
// Elements of ℚ(ω) are a + b·ω with a,b ∈ ℚ, and ω² = -ω - 1.

/// Minimal polynomial for a primitive cube root of unity: p(x) = x² + x + 1.
pub struct PrimCubeRootUnity;

impl MinimalPoly<Rational> for PrimCubeRootUnity {
    open spec fn degree() -> nat { 2 }

    open spec fn coeffs() -> Seq<Rational> {
        seq![
            Rational::from_int_spec(1),   // c_0 = 1
            Rational::from_int_spec(1),   // c_1 = 1
        ]
        // p(x) = x² + 1·x + 1
    }

    proof fn axiom_degree_ge_2() { }

    proof fn axiom_coeffs_len() { }
}

/// Type alias for ℚ(ω) where ω is a primitive cube root of unity.
pub type QCubeRootUnity = SpecFieldExt<Rational, PrimCubeRootUnity>;

} // verus!
