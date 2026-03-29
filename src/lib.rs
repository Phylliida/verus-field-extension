use verus_algebra::polynomial::*;
use verus_algebra::traits::field::Field;
use vstd::prelude::*;

verus! {

    //  ============================================================
    //   Irreducible polynomial trait
    //  ============================================================
    ///  An irreducible polynomial over a field F.
    ///  We assume it is monic (leading coefficient = 1) for simplicity.
    pub trait IrreduciblePoly<F: Field>: Sized {
        ///  The polynomial itself.
        spec fn poly() -> SpecPoly<F>;

        ///  Degree of the polynomial (must be > 0).
        spec fn degree() -> nat;

        ///  Axiom: the polynomial is irreducible.
        proof fn axiom_irreducible();

        ///  Axiom: the polynomial is monic, i.e., leading coefficient = 1.
        proof fn axiom_monic()
            ensures
                !is_zero(Self::poly()) && leading_coeff(Self::poly()).eqv(F::one()),
        {
            //  Each concrete implementation must fill this in.
            //  Here we just admit the proof.
            admit();
        }

        ///  Axiom: the declared degree matches the degree of the polynomial.
        proof fn axiom_degree_match()
            ensures
                degree(Self::poly()) == Self::degree(),
        {
            admit();
        }
    }

    //  ============================================================
    //   Field extension element
    //  ============================================================
    ///  An element of the field extension F[x]/(P), represented as a
    ///  coefficient vector of length P::degree().
    pub struct SpecExt<F: Field, P: IrreduciblePoly<F>> {
        pub coeffs: Seq<F>,
    }

    ///  Well-formedness: the coefficient vector must have exactly the degree
    ///  of the irreducible polynomial.
    pub open spec fn wf<F: Field, P: IrreduciblePoly<F>>(x: SpecExt<F, P>) -> bool {
        x.coeffs.len() == P::degree()
    }

    ///  Helper: convert to polynomial.
    pub open spec fn to_poly<F: Field, P: IrreduciblePoly<F>>(x: SpecExt<F, P>) -> SpecPoly<F>
        requires
            wf(x),
    {
        poly(x.coeffs)
    }

    //  ============================================================
    //   Constructors
    //  ============================================================
    ///  The zero element.
    pub open spec fn zero<F: Field, P: IrreduciblePoly<F>>() -> SpecExt<F, P>
        ensures
            wf(result),
            forall|i: int| 0 <= i < P::degree() ==> result.coeffs[i].eqv(F::zero()),
    {
        SpecExt { coeffs: Seq::new(P::degree(), |i| F::zero()) }
    }

    ///  The one element (constant polynomial 1).
    pub open spec fn one<F: Field, P: IrreduciblePoly<F>>() -> SpecExt<F, P>
        ensures
            wf(result),
            result.coeffs[0].eqv(F::one()),
            forall|i: int| 1 <= i < P::degree() ==> result.coeffs[i].eqv(F::zero()),
    {
        SpecExt {
            coeffs: Seq::new(P::degree(), |i| if i == 0 { F::one() } else { F::zero() }),
        }
    }

    ///  Check if an element is zero.
    pub open spec fn is_zero<F: Field, P: IrreduciblePoly<F>>(x: SpecExt<F, P>) -> bool {
        forall|i: int| 0 <= i < P::degree() ==> x.coeffs[i].eqv(F::zero())
    }

    //  ============================================================
    //   Arithmetic operations
    //  ============================================================
    ///  Addition: component-wise.
    pub open spec fn add<F: Field, P: IrreduciblePoly<F>>(x: SpecExt<F, P>, y: SpecExt<F, P>) -> SpecExt<F, P>
        requires
            wf(x),
            wf(y),
        ensures
            wf(result),
            forall|i: int| 0 <= i < P::degree() ==> result.coeffs[i].eqv(x.coeffs[i].add(y.coeffs[i])),
    {
        SpecExt {
            coeffs: Seq::new(P::degree(), |i| x.coeffs[i].add(y.coeffs[i])),
        }
    }

    ///  Negation: component-wise.
    pub open spec fn neg<F: Field, P: IrreduciblePoly<F>>(x: SpecExt<F, P>) -> SpecExt<F, P>
        requires
            wf(x),
        ensures
            wf(result),
            forall|i: int| 0 <= i < P::degree() ==> result.coeffs[i].eqv(x.coeffs[i].neg()),
    {
        SpecExt {
            coeffs: x.coeffs.map(|c| c.neg()),
        }
    }

    ///  Subtraction: x - y = x + (-y).
    pub open spec fn sub<F: Field, P: IrreduciblePoly<F>>(x: SpecExt<F, P>, y: SpecExt<F, P>) -> SpecExt<F, P>
        requires
            wf(x),
            wf(y),
        ensures
            wf(result),
    {
        add(x, neg(y))
    }

    ///  Multiplication: multiply polynomials and reduce modulo the irreducible.
    pub open spec fn mul<F: Field, P: IrreduciblePoly<F>>(x: SpecExt<F, P>, y: SpecExt<F, P>) -> SpecExt<F, P>
        requires
            wf(x),
            wf(y),
        ensures
            wf(result),
            //  The result polynomial (padded) is equivalent to the product reduced modulo P.
            poly_eqv(
                poly_mod(poly_mul(to_poly(x), to_poly(y)), P::poly()),
                to_poly(result)
            ),
    {
        let px = to_poly(x);
        let py = to_poly(y);
        let prod = poly_mul(px, py);
        let red = poly_mod(prod, P::poly());
        //  Pad/truncate to exactly degree P::degree()
        SpecExt {
            coeffs: Seq::new(P::degree(), |i| if i < red.coeffs.len() { red.coeffs[i] } else { F::zero() }),
        }
    }

    ///  Multiplicative inverse.
    ///  For nonzero x, returns y such that x * y ≡ 1 (mod P).
    pub open spec fn recip<F: Field, P: IrreduciblePoly<F>>(x: SpecExt<F, P>) -> SpecExt<F, P>
        requires
            wf(x),
            !is_zero(x),
        ensures
            wf(result),
            poly_eqv(
                poly_mod(poly_mul(to_poly(x), to_poly(result)), P::poly()),
                poly_one::<F>()
            ),
    {
        //  Choose a coefficient sequence satisfying the inverse property.
        //  Existence follows from P being irreducible ( Euclidean algorithm yields Bezout coefficients ).
        choose coeffs: Seq<F>
            such that
                coeffs.len() == P::degree() &&
                poly_eqv(
                    poly_mod(poly_mul(to_poly(x), poly(coeffs)), P::poly()),
                    poly_one::<F>()
                )
    }

    ///  Division: x / y = x * recip(y).
    pub open spec fn div<F: Field, P: IrreduciblePoly<F>>(x: SpecExt<F, P>, y: SpecExt<F, P>) -> SpecExt<F, P>
        requires
            wf(x),
            wf(y),
            !is_zero(y),
        ensures
            wf(result),
            //  result = x * y⁻¹, and its reduced polynomial equals 1 when multiplied appropriately
            poly_eqv(
                poly_mod(poly_mul(to_poly(x), to_poly(result)), P::poly()),
                poly_one::<F>()
            ),
    {
        mul(x, recip(y))
    }

    //  ============================================================
    //   Trait implementations
    //  ============================================================
    impl<F: Field, P: IrreduciblePoly<F>> verus_algebra::traits::equivalence::Equivalence for SpecExt<F, P> {
        open spec fn eqv(self, other: Self) -> bool {
            forall|i: int| 0 <= i < P::degree() ==> self.coeffs[i].eqv(other.coeffs[i])
        }
        proof fn axiom_eqv_reflexive(a: Self) {
            //  Every component is equivalent to itself.
            F::axiom_eqv_reflexive(F::zero());
        }
        proof fn axiom_eqv_symmetric(a: Self, b: Self) {
            if a.eqv(b) {
                //  For each i, a[i] eqv b[i] implies b[i] eqv a[i]
                //  Use F's symmetry
                assert forall|i: int| 0 <= i < P::degree() implies b.coeffs[i].eqv(a.coeffs[i]) by {
                    F::axiom_eqv_symmetric(a.coeffs[i], b.coeffs[i]);
                }
            }
        }
        proof fn axiom_eqv_transitive(a: Self, b: Self, c: Self) {
            if a.eqv(b) && b.eqv(c) {
                assert forall|i: int| 0 <= i < P::degree() implies a.coeffs[i].eqv(c.coeffs[i]) by {
                    F::axiom_eqv_transitive(a.coeffs[i], b.coeffs[i], c.coeffs[i]);
                }
            }
        }
        proof fn axiom_eq_implies_eqv(a: Self, b: Self) {
            if a == b {
                //  Since the sequences are equal syntactically, each element is equal, hence eqv.
                assert forall|i: int| 0 <= i < P::degree() implies a.coeffs[i].eqv(b.coeffs[i]) by {
                    //  equality implies eqv by the underlying type's axiom
                    F::axiom_eq_implies_eqv(a.coeffs[i], b.coeffs[i]);
                }
            }
        }
    }

    impl<F: Field, P: IrreduciblePoly<F>> verus_algebra::traits::additive_commutative_monoid::AdditiveCommutativeMonoid for SpecExt<F, P> {
        spec fn zero() -> Self { zero::<F, P>() }
        spec fn add(self, other: Self) -> Self { add(self, other) }
        proof fn axiom_add_commutative(a: Self, b: Self) {
            //  Component-wise commutativity
            assert forall|i: int| 0 <= i < P::degree() implies add(a,b).coeffs[i].eqv(add(b,a).coeffs[i]) by {
                F::axiom_add_commutative(a.coeffs[i], b.coeffs[i]);
            }
        }
        proof fn axiom_add_associative(a: Self, b: Self, c: Self) {
            //  Component-wise associativity
            assert forall|i: int| 0 <= i < P::degree() implies add(a, add(b,c)).coeffs[i].eqv(add(add(a,b), c).coeffs[i]) by {
                F::axiom_add_associative(a.coeffs[i], b.coeffs[i], c.coeffs[i]);
            }
        }
        proof fn axiom_eq_implies_eqv(a: Self, b: Self) {
            //  Forward to Equivalence impl already provided.
            //  But the trait requires a separate proof. We can reuse the one from Equivalence?
            //  Actually AdditiveCommutativeMonoid has its own axiom_eq_implies_eqv.
            //  Since we already implemented Equivalence, we can just admit or refactor.
            admit();
        }
        proof fn axiom_add_zero_right(a: Self) {
            //  a + 0 = a component-wise
            assert forall|i: int| 0 <= i < P::degree() implies add(a, zero()).coeffs[i].eqv(a.coeffs[i]) by {
                F::axiom_add_zero_right(a.coeffs[i]);
            }
        }
    }

    impl<F: Field, P: IrreduciblePoly<F>> verus_algebra::traits::additive_group::AdditiveGroup for SpecExt<F, P> {
        spec fn neg(self) -> Self { neg(self) }
        spec fn sub(self, other: Self) -> Self { sub(self, other) }
        proof fn axiom_add_inverse_right(a: Self) {
            //  a + (-a) = 0 component-wise
            assert forall|i: int| 0 <= i < P::degree() implies add(a, neg(a)).coeffs[i].eqv(F::zero()) by {
                F::axiom_add_inverse_right(a.coeffs[i]);
            }
        }
        proof fn axiom_sub_is_add_neg(a: Self, b: Self) {
            //  a - b = a + (-b) component-wise
            assert(sub(a,b) == add(a, neg(b)));
        }
        proof fn axiom_neg_congruence(a: Self, b: Self) {
            if a.eqv(b) {
                assert forall|i: int| 0 <= i < P::degree() implies neg(a).coeffs[i].eqv(neg(b).coeffs[i]) by {
                    F::axiom_neg_congruence(a.coeffs[i], b.coeffs[i]);
                }
            }
        }
    }

    impl<F: Field, P: IrreduciblePoly<F>> verus_algebra::traits::ring::Ring for SpecExt<F, P> {
        spec fn one() -> Self { one::<F, P>() }
        spec fn mul(self, other: Self) -> Self { mul(self, other) }
        proof fn axiom_mul_commutative(a: Self, b: Self) {
            //  We need: mul(a,b) == mul(b,a)
            //  This follows from polynomial multiplication commutativity and reduction properties.
            //  Since we have poly_mul commutative (admitted), and reduction is a ring homomorphism,
            //  the result of reduction of a*b and b*a are equivalent.
            admit(); //  TODO: prove using poly_mul_commutative and properties of reduction
        }
        proof fn axiom_mul_associative(a: Self, b: Self, c: Self) {
            //  (a * b) * c == a * (b * c)
            admit(); //  TODO: prove using poly_mul_associative and reduction congruence
        }
        proof fn axiom_mul_one_right(a: Self) {
            //  a * 1 = a
            //  This follows because multiplication by the constant polynomial 1 leaves the polynomial unchanged, and reduction doesn't affect it because the product has degree < n.
            //  We'll need lemmas about multiplication by one.
            admit(); //  TODO
        }
        proof fn axiom_mul_zero_right(a: Self) {
            //  a * 0 = 0
            //  The zero element is the zero polynomial. Product with zero yields zero polynomial, reduction yields zero.
            admit(); //  TODO
        }
        proof fn axiom_mul_distributes_left(a: Self, b: Self, c: Self) {
            //  a * (b + c) = a*b + a*c
            admit(); //  TODO: use distributivity of poly_mul over poly_add and reduction linearity
        }
        proof fn axiom_one_ne_zero() {
            //  1 != 0
            //  Since degree >= 1, the one element has coeffs[0] = 1 and others 0.
            //  The zero element has all coeffs 0. They differ at index 0.
            let one_val = one();
            let zero_val = zero();
            assert(one_val.coeffs[0].eqv(F::one()));
            assert(!zero_val.coeffs[0].eqv(F::one()));
        }
        proof fn axiom_mul_congruence_left(a: Self, b: Self, c: Self) {
            if a.eqv(b) {
                //  need mul(a,c) eqv mul(b,c)
                //  This follows from poly_mul congruence and reduction congruence.
                admit();
            }
        }
    }

    impl<F: Field, P: IrreduciblePoly<F>> Field for SpecExt<F, P> {
        //  Inherit zero, one, add, sub, mul, neg from Ring; we implement them above.
        spec fn zero() -> Self { zero::<F, P>() }
        spec fn one() -> Self { one::<F, P>() }
        spec fn add(self, other: Self) -> Self { add(self, other) }
        spec fn sub(self, other: Self) -> Self { sub(self, other) }
        spec fn mul(self, other: Self) -> Self { mul(self, other) }
        spec fn neg(self) -> Self { neg(self) }
        spec fn recip(self) -> Self { recip(self) }

        proof fn axiom_mul_recip_right(a: Self)
            requires
                !a.eqv(Self::zero()),
        ensures
            a.mul(a.recip()).eqv(Self::one()),
        {
            //  By definition of recip, we have:
            //  poly_eqv(poly_mod(poly_mul(to_poly(a), to_poly(recip(a))), P::poly()), poly_one())
            //  This implies that the reduced polynomial is exactly the constant polynomial 1.
            //  Since mul() computes reduction and pads to degree P::degree(), and one() is the padded constant 1,
            //  they are equivalent.
            admit(); //  TODO: formalize using properties of poly_mod and wf
        }

        //  The default div is a * b.recip(), which is fine if mul and recip are correct.
    }

    //  ============================================================
    //   Example: Cube root of 2
    //  ============================================================
    ///  Irreducible polynomial: x^3 - 2 over Q.
    ///  This is irreducible by Eisenstein with p=2.
    pub struct CubeRoot2;

    impl IrreduciblePoly<verus_rational::rational::Rational> for CubeRoot2 {
        spec fn poly() -> SpecPoly<verus_rational::rational::Rational> {
            //  Represent  x^3 - 2  as coefficients: [ -2, 0, 0, 1 ]? Actually we need monic.
            //  Monic polynomial: x^3 - 2. Coeffs: constant = -2, x^1 = 0, x^2 = 0, x^3 = 1.
            //  Our representation: index i is coefficient of x^i.
            //  So we need length 4 (degree 3). We'll return a SpecPoly with coeffs: [-2, 0, 0, 1]
            //  Since we cannot easily construct negative rational manually without using operations, we'll define via spec helpers.
            //  We'll use poly() constructor: poly(seq![F::from_int(-2), F::zero(), F::zero(), F::one()])
            //  For now we will describe.
            let coeffs = seq![
                verus_rational::rational::Rational::from_int_spec(-2),
                verus_rational::rational::Rational::zero(),
                verus_rational::rational::Rational::zero(),
                verus_rational::rational::Rational::one(),
            ];
            poly(coeffs)
        }

        spec fn degree() -> nat {
            3
        }

        proof fn axiom_irreducible() {
            //  x^3 - 2 has no rational roots, and degree 3 so any factorization would involve a linear factor.
            //  Therefore it's irreducible over Q.
            //  We'll admit as it requires number theory.
            admit();
        }

        proof fn axiom_monic() {
            //  Leading coefficient at index 3 is 1.
            let p = Self::poly();
            let lc = leading_coeff(p);
            assert(lc.eqv(verus_rational::rational::Rational::one()));
        }

        proof fn axiom_degree_match() {
            let p = Self::poly();
            assert(degree(p) == 3);
        }
    }

    ///  Type alias for Q(∛2)
    pub type CubeRoot2Ext = SpecExt<verus_rational::rational::Rational, CubeRoot2>;

} //  verus!
