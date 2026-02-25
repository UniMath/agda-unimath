# Parametricity of the booleans

```agda
module foundation.parametricity-booleans where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.axiom-of-choice
open import foundation.booleans
open import foundation.constant-maps
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.diaconescus-theorem
open import foundation.double-negation
open import foundation.double-negation-stable-propositions
open import foundation.empty-types
open import foundation.evaluation-functions
open import foundation.function-extensionality
open import foundation.functoriality-coproduct-types
open import foundation.law-of-excluded-middle
open import foundation.logical-equivalences
open import foundation.negated-equality
open import foundation.parametric-types
open import foundation.propositional-extensionality
open import foundation.propositional-truncations
open import foundation.subuniverse-parametric-types
open import foundation.subuniverses
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-empty-type
open import foundation.unit-type
open import foundation.univalence
open import foundation.universal-property-equivalences
open import foundation.universe-levels
open import foundation.weak-limited-principle-of-omniscience

open import foundation-core.cartesian-product-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.negation
open import foundation-core.propositions
open import foundation-core.retractions
open import foundation-core.sections

open import orthogonal-factorization-systems.coproducts-null-types
open import orthogonal-factorization-systems.null-types

open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
open import univalent-combinatorics.subcounting
open import univalent-combinatorics.subfinite-types
```

</details>

## Idea

The [booleans](foundation.booleans.md) are said to be
[parametric](foundation.parametric-types.md) if the constant map at the
universe, `bool → (𝒰 → bool)`, is an
[equivalence](foundation-core.equivalences.md).

We consider consequences of assuming the booleans are parametric, and hypotheses
under which the booleans are parametric:

1. If the booleans are parametric then the law of excluded middle does not hold.
2. If the booleans are parametric then the axiom of choice does not hold.
3. If the weak limited principle of omniscience does not hold then the booleans
   are parametric.
4. If the booleans are parametric then parametric types are closed under
   coproducts.

## Properties

### Parametricity of the booleans contradicts excluded middle

```agda
module _
  {l : Level}
  where abstract

  is-true-map-bool-LEM-Double-Negation-Stable-Prop :
    level-LEM l →
    Double-Negation-Stable-Prop l →
    bool
  is-true-map-bool-LEM-Double-Negation-Stable-Prop lem P =
    rec-coproduct
      ( λ _ → true)
      ( λ _ → false)
      ( lem (prop-Double-Negation-Stable-Prop P))

  compute-is-true-map-bool-LEM-Double-Negation-Stable-Prop-raise-empty :
    (lem : level-LEM l) →
    is-true-map-bool-LEM-Double-Negation-Stable-Prop
      lem
      ( raise-empty-Double-Negation-Stable-Prop l) ＝ false
  compute-is-true-map-bool-LEM-Double-Negation-Stable-Prop-raise-empty lem =
    ind-coproduct
      ( λ d → rec-coproduct (λ _ → true) (λ _ → false) d ＝ false)
      ( λ p → ex-falso (is-empty-raise-empty p))
      ( λ _ → refl)
      ( lem
        ( prop-Double-Negation-Stable-Prop
          ( raise-empty-Double-Negation-Stable-Prop l)))

  compute-is-true-map-bool-LEM-Double-Negation-Stable-Prop-raise-unit :
    (lem : level-LEM l) →
    is-true-map-bool-LEM-Double-Negation-Stable-Prop
      lem
      ( raise-unit-Double-Negation-Stable-Prop l) ＝ true
  compute-is-true-map-bool-LEM-Double-Negation-Stable-Prop-raise-unit lem =
    ind-coproduct
      ( λ d → rec-coproduct (λ _ → true) (λ _ → false) d ＝ true)
      ( λ _ → refl)
      ( λ p → ex-falso (p raise-star))
      ( lem
        ( prop-Double-Negation-Stable-Prop
          ( raise-unit-Double-Negation-Stable-Prop l)))

  is-constant-map-is-¬¬-parametric-bool :
    is-null (Double-Negation-Stable-Prop l) bool →
    (f : Double-Negation-Stable-Prop l → bool) →
    (P Q : Double-Negation-Stable-Prop l) →
    f P ＝ f Q
  is-constant-map-is-¬¬-parametric-bool H f P Q =
    ( inv
      ( htpy-eq
        ( is-section-map-inv-equiv
          ( const (Double-Negation-Stable-Prop l) , H)
          ( f))
        ( P))) ∙
    ( htpy-eq
      ( is-section-map-inv-equiv
        ( const (Double-Negation-Stable-Prop l) , H)
        ( f))
      ( Q))

  no-LEM-is-¬¬-parametric-bool :
    is-subuniverse-parametric
      {l1 = lzero} {l2 = l} {l3 = l}
      ( is-double-negation-stable-prop-Prop)
      ( bool) →
    ¬ level-LEM l
  no-LEM-is-¬¬-parametric-bool H lem =
    neq-true-false-bool
      ( ( inv
          ( compute-is-true-map-bool-LEM-Double-Negation-Stable-Prop-raise-unit
            ( lem))) ∙
        ( is-constant-map-is-¬¬-parametric-bool
          ( H)
          ( is-true-map-bool-LEM-Double-Negation-Stable-Prop lem)
          ( raise-unit-Double-Negation-Stable-Prop l)
          ( raise-empty-Double-Negation-Stable-Prop l)) ∙
        ( compute-is-true-map-bool-LEM-Double-Negation-Stable-Prop-raise-empty
          ( lem)))

  no-LEM-is-parametric-bool :
    is-parametric l bool → ¬ level-LEM l
  no-LEM-is-parametric-bool H =
    no-LEM-is-¬¬-parametric-bool
      ( is-¬¬-parametric-is-parametric H)
```

### Parametricity of the booleans contradicts the axiom of choice

```agda
abstract
  no-AC0-is-parametric-bool :
    {l : Level} → is-parametric l bool → ¬ level-AC0 l l
  no-AC0-is-parametric-bool H ac =
    no-LEM-is-¬¬-parametric-bool
      ( is-¬¬-parametric-is-parametric H)
      ( theorem-Diaconescu ac)
```

### Coproduct closure of parametric types is equivalent to parametricity of the booleans

```agda
abstract
  is-parametric-coproduct-is-parametric-bool :
    {l : Level} →
    is-parametric l bool →
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-parametric l A → is-parametric l B → is-parametric l (A + B)
  is-parametric-coproduct-is-parametric-bool {l} H HA HB =
    is-null-coproduct-is-null-bool (UU l) H HA HB

  is-parametric-bool-is-parametric-coproduct :
    {l : Level} →
    ( {l1 l2 : Level} {A : UU l1} {B : UU l2} →
      is-parametric l A → is-parametric l B → is-parametric l (A + B)) →
    is-parametric l bool
  is-parametric-bool-is-parametric-coproduct {l} =
    coproduct-closed-null-implies-is-null-bool {Y = UU l}

module _
  {l2 l3 : Level} (K : subuniverse l2 l3)
  where abstract

  is-subuniverse-parametric-coproduct-is-subuniverse-parametric-bool :
    is-subuniverse-parametric K bool →
    {l4 l5 : Level} {A : UU l4} {B : UU l5} →
    is-subuniverse-parametric K A →
    is-subuniverse-parametric K B →
    is-subuniverse-parametric K (A + B)
  is-subuniverse-parametric-coproduct-is-subuniverse-parametric-bool
    H HA HB =
    is-null-coproduct-is-null-bool (type-subuniverse K) H HA HB

  is-subuniverse-parametric-bool-is-subuniverse-parametric-coproduct :
    ( {l4 l5 : Level} {A : UU l4} {B : UU l5} →
      is-subuniverse-parametric K A →
      is-subuniverse-parametric K B →
      is-subuniverse-parametric K (A + B)) →
    is-subuniverse-parametric K bool
  is-subuniverse-parametric-bool-is-subuniverse-parametric-coproduct =
    coproduct-closed-null-implies-is-null-bool {Y = type-subuniverse K}
```

### Parametricity of the booleans implies parametricity of finite types

```agda
abstract
  is-parametric-Fin-is-parametric-bool :
    {l : Level} →
    is-parametric l bool →
    (n : ℕ) → is-parametric l (Fin n)
  is-parametric-Fin-is-parametric-bool {l} =
    is-null-Fin-is-null-bool (UU l)

  is-parametric-is-finite-is-parametric-bool :
    {l1 l2 : Level} {X : UU l1} →
    is-parametric l2 bool →
    is-finite X →
    is-parametric l2 X
  is-parametric-is-finite-is-parametric-bool {l2 = l2} =
    is-null-is-finite-is-null-bool (UU l2)

  is-parametric-type-Finite-Type-is-parametric-bool :
    {l1 l2 : Level} →
    is-parametric l2 bool →
    (X : Finite-Type l1) →
    is-parametric l2 (type-Finite-Type X)
  is-parametric-type-Finite-Type-is-parametric-bool {l2 = l2} =
    is-null-type-Finite-Type-is-null-bool (UU l2)
```

### Parametricity of the booleans implies parametricity of subfinite types

```agda
abstract
  is-parametric-has-subcount-is-parametric-bool :
    {l1 l2 : Level} {X : UU l1} →
    is-parametric l2 bool →
    subcount X →
    is-parametric l2 X
  is-parametric-has-subcount-is-parametric-bool H (n , e) =
    is-parametric-emb e (is-parametric-Fin-is-parametric-bool H n)

  is-parametric-is-subfinite-is-parametric-bool :
    {l1 l2 : Level} {X : UU l1} →
    is-parametric l2 bool →
    is-subfinite X →
    is-parametric l2 X
  is-parametric-is-subfinite-is-parametric-bool {l2 = l2} {X = X} H s =
    apply-universal-property-trunc-Prop
      ( s)
      ( is-parametric-Prop l2 X)
      ( is-parametric-has-subcount-is-parametric-bool H)

  is-parametric-type-Subfinite-Type-is-parametric-bool :
    {l1 l2 : Level} →
    is-parametric l2 bool →
    (X : Subfinite-Type l1) →
    is-parametric l2 (type-Subfinite-Type X)
  is-parametric-type-Subfinite-Type-is-parametric-bool H (X , eX) =
    is-parametric-is-subfinite-is-parametric-bool H eX
```

### A WLPO-based separation principle for booleans

If there exists a function `f : I → bool` together with elements `X` and `Y` of
`I` such that `f X ≠ f Y`, and moreover there is some assignment of propositions
to `I`, `χ : Prop → I` that sends true propositions to `X` and false
propositions to `Y`, then WLPO holds. For `I` equal to the universe, there is
such a map given by splitting at any given proposition:

```text
  χ P ≔ (P × X) + ((¬ P) × Y)
```

Therefore, if WLPO does not hold, then `f` must send `X` and `Y` to the same
element in `bool`, and hence `bool` is parametric.

```agda
module _
  {l1 : Level} {I : UU l1}
  (f : I → bool)
  {X Y : I}
  (fX≠fY : f X ≠ f Y)
  (χ : Prop lzero → I)
  (eq-χ-true : (P : Prop lzero) → type-Prop P → χ P ＝ X)
  (eq-χ-false : (P : Prop lzero) → ¬ type-Prop P → χ P ＝ Y)
  where abstract

  is-decidable-split-on-double-negation-stable-prop :
    (P : Prop lzero) →
    (¬¬ type-Prop P → type-Prop P) →
    is-decidable (type-Prop P)
  is-decidable-split-on-double-negation-stable-prop P H =
    map-coproduct
      ( λ p → H (λ np → fX≠fY (inv p ∙ ap f (eq-χ-false P np))))
      ( λ np p → np (ap f (eq-χ-true P p)))
      ( has-decidable-equality-bool (f (χ P)) (f X))

  bool-WLPO-separating-map-split : bool-WLPO
  bool-WLPO-separating-map-split g =
    is-decidable-split-on-double-negation-stable-prop
      ( Π-Prop ℕ (λ n → is-true-Prop (g n)))
      ( λ nn-all-g n →
        double-negation-elim-is-decidable
          ( has-decidable-equality-bool (g n) true)
          ( λ nn-gn → nn-all-g (λ all-g → nn-gn (all-g n))))

abstract
  separate-boolean-map-split-on-prop-bool-WLPO :
    {l1 : Level} {I : UU l1} →
    ¬ bool-WLPO →
    (f : I → bool) →
    (X Y : I) →
    (χ : (f X ≠ f Y) → Prop lzero → I) →
    ( (fX≠fY : f X ≠ f Y) (P : Prop lzero) →
      type-Prop P → χ fX≠fY P ＝ X) →
    ( (fX≠fY : f X ≠ f Y) (P : Prop lzero) →
      ¬ type-Prop P → χ fX≠fY P ＝ Y) →
    f X ＝ f Y
  separate-boolean-map-split-on-prop-bool-WLPO
    nwlpo f X Y χ eq-χ-true eq-χ-false =
    rec-coproduct
      ( id)
      ( λ fX≠fY →
        ex-falso
          ( nwlpo
            ( bool-WLPO-separating-map-split
              ( f)
              ( fX≠fY)
              ( χ fX≠fY)
              ( eq-χ-true fX≠fY)
              ( eq-χ-false fX≠fY))))
      ( has-decidable-equality-bool (f X) (f Y))

  compute-split-on-prop-true :
    {l1 l2 l3 : Level} (P : Prop l1) {X : UU l2} {Y : UU l3} →
    type-Prop P → ((type-Prop P × X) + ((¬ type-Prop P) × Y)) ≃ X
  compute-split-on-prop-true P {X = X} {Y = Y} p =
    ( left-unit-law-product-is-contr
      ( is-proof-irrelevant-is-prop (is-prop-type-Prop P) p)) ∘e
    ( right-unit-law-coproduct-is-empty
      ( type-Prop P × X)
      ( (¬ type-Prop P) × Y)
      ( λ z → (pr1 z) p))

  compute-split-on-prop-false :
    {l1 l2 l3 : Level} (P : Prop l1) {X : UU l2} {Y : UU l3} →
    ¬ type-Prop P → ((type-Prop P × X) + ((¬ type-Prop P) × Y)) ≃ Y
  compute-split-on-prop-false P {X = X} {Y = Y} np =
    ( left-unit-law-product-is-contr
      (is-proof-irrelevant-is-prop (is-property-is-empty) np)) ∘e
    ( left-unit-law-coproduct-is-empty
      ( type-Prop P × X)
      ( (¬ type-Prop P) × Y)
      ( λ z → np (pr1 z)))
```

### Rejecting WLPO requires accepting that the booleans are parametric

This depends on the univalence axiom.

```agda
split-on-prop :
  {l : Level} (f : UU l → bool) {X Y : UU l} → Prop lzero → UU l
split-on-prop f {X} {Y} P = (type-Prop P × X) + ((¬ type-Prop P) × Y)

abstract
  rice-contrapositive-bool-WLPO :
    {l : Level} →
    ¬ bool-WLPO →
    (f : UU l → bool) →
    (X Y : UU l) → f X ＝ f Y
  rice-contrapositive-bool-WLPO nwlpo f X Y =
    separate-boolean-map-split-on-prop-bool-WLPO nwlpo f X Y
      ( λ _ → split-on-prop f {X} {Y})
      ( λ _ P p → eq-equiv (compute-split-on-prop-true P p))
      ( λ _ P np → eq-equiv (compute-split-on-prop-false P np))

  is-parametric-bool-no-bool-WLPO :
    {l : Level} → ¬ bool-WLPO → is-parametric l bool
  is-parametric-bool-no-bool-WLPO {l} nwlpo =
    is-equiv-is-invertible
      ( ev (raise-empty l))
      ( λ f →
        eq-htpy
          ( λ X →
            inv (rice-contrapositive-bool-WLPO nwlpo f X (raise-empty l))))
      ( refl-htpy)
```

### Rejecting WLPO requires accepting that the booleans are proposition-parametric

We repeat the proof to avoid using univalence. In this case we only require
propositional extensionality.

```agda
module _
  {l : Level}
  (f : Prop l → bool)
  {X Y : Prop l}
  where abstract

  split-on-prop-Prop : Prop lzero → Prop l
  pr1 (split-on-prop-Prop P) =
    (type-Prop P × type-Prop X) + ((¬ type-Prop P) × type-Prop Y)
  pr2 (split-on-prop-Prop P) =
    is-prop-coproduct
      ( λ z w → (pr1 w) (pr1 z))
      ( is-prop-product (is-prop-type-Prop P) (is-prop-type-Prop X))
      ( is-prop-product (is-property-is-empty) (is-prop-type-Prop Y))

abstract
  rice-contrapositive-prop-bool-WLPO :
    {l : Level} →
    ¬ bool-WLPO →
    (f : Prop l → bool) (X Y : Prop l) → f X ＝ f Y
  rice-contrapositive-prop-bool-WLPO nwlpo f X Y =
    separate-boolean-map-split-on-prop-bool-WLPO nwlpo f X Y
      ( λ _ → split-on-prop-Prop f {X} {Y})
      ( λ _ P p →
        eq-iff'
          ( split-on-prop-Prop f P)
          ( X)
          ( iff-equiv (compute-split-on-prop-true P p)))
      ( λ _ P np →
        eq-iff'
          ( split-on-prop-Prop f P)
          ( Y)
          ( iff-equiv (compute-split-on-prop-false P np)))

  is-prop-parametric-bool-no-bool-WLPO :
    {l : Level} → ¬ bool-WLPO → is-null (Prop l) bool
  is-prop-parametric-bool-no-bool-WLPO {l} nwlpo =
    is-equiv-is-invertible
      ( ev (raise-empty-Prop l))
      ( λ f →
        eq-htpy
          ( λ P →
            inv
              ( rice-contrapositive-prop-bool-WLPO
                ( nwlpo)
                ( f)
                ( P)
                ( raise-empty-Prop l))))
      ( refl-htpy)
```

## See also

- [The parametricity axiom](foundation.parametricity-axiom.md)
- [Parametric types](foundation.parametric-types.md)
