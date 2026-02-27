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
open import foundation.decidable-propositions
open import foundation.decidable-subtypes
open import foundation.decidable-type-families
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
open import foundation.types-with-decidable-dependent-product-types
open import foundation.types-with-decidable-universal-quantifications
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

We consider consequences of assuming the booleans are parametric:

1. If the booleans are parametric then the law of excluded middle does not hold.
2. If the booleans are parametric then the axiom of choice does not hold.
3. If the booleans are parametric then parametric types are closed under
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
    is-null-bool-is-null-coproduct {Y = UU l}

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
    is-null-bool-is-null-coproduct {Y = type-subuniverse K}
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

### If some type refutes decidable Π-types then the booleans are parametric

```agda
abstract
  is-parametric-bool-not-has-decidable-∀-Level :
    {l : Level} {A : UU l} →
    ¬ has-decidable-∀-Level l A → is-parametric l bool
  is-parametric-bool-not-has-decidable-∀-Level ¬d∀A =
    is-parametric-not-has-decidable-∀-Discrete-Type ¬d∀A bool-Discrete-Type

  is-parametric-lzero-bool-no-WLPO :
    ¬ level-WLPO lzero → is-parametric lzero bool
  is-parametric-lzero-bool-no-WLPO =
    is-parametric-bool-not-has-decidable-∀-Level
```

## See also

- [The parametricity axiom](foundation.parametricity-axiom.md)
- [Parametric types](foundation.parametric-types.md)
