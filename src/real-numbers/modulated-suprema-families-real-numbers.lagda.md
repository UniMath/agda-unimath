# Modulated suprema of families of real numbers

```agda
module real-numbers.modulated-suprema-families-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.axiom-of-countable-choice
open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.functoriality-dependent-pair-types
open import foundation.function-types
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.least-upper-bounds-large-posets
open import order-theory.upper-bounds-large-posets

open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.strict-inequality-real-numbers
open import real-numbers.suprema-families-real-numbers
```

</details>

## Idea

A
{{#concept "modulated supremum" Disambiguation="of families of real numbers" Agda=is-modulated-supremum-family-ℝ}}
`x` of a family of [real numbers](real-numbers.dedekind-real-numbers.md)
`y : I → ℝ` is an [upper bound](order-theory.upper-bounds-large-posets.md) of
`y` for which there [exists](foundation.existential-quantification.md) a
**supremum modulus**: a function `m : ℚ⁺ → I` such that for each `ε : ℚ⁺` we
have `x - ε < y(m ε)`.

## Definition

### Supremum moduli

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} (y : I → ℝ l2) (x : ℝ l3)
  where

  supremum-modulus-family-ℝ : UU (l1 ⊔ l2 ⊔ l3)
  supremum-modulus-family-ℝ =
      ( is-upper-bound-family-of-elements-Large-Poset ℝ-Large-Poset y x) ×
      ( (ε : ℚ⁺) → Σ I (λ i → le-ℝ (x -ℝ real-ℚ⁺ ε) (y i)))

  is-upper-bound-supremum-modulus-family-ℝ :
    supremum-modulus-family-ℝ →
    is-upper-bound-family-of-elements-Large-Poset
      ( ℝ-Large-Poset)
      ( y)
      ( x)
  is-upper-bound-supremum-modulus-family-ℝ = pr1

  modulus-supremum-modulus-family-ℝ :
    supremum-modulus-family-ℝ → ℚ⁺ → I
  modulus-supremum-modulus-family-ℝ μ = pr1 ∘ pr2 μ

  le-modulus-supremum-modulus-family-ℝ :
    (μ : supremum-modulus-family-ℝ) →
    (ε : ℚ⁺) → le-ℝ (x -ℝ real-ℚ⁺ ε) (y (modulus-supremum-modulus-family-ℝ μ ε))
  le-modulus-supremum-modulus-family-ℝ μ = pr2 ∘ pr2 μ

  is-approximated-below-supremum-modulus-family-ℝ :
    supremum-modulus-family-ℝ →
    is-approximated-below-family-ℝ y x
  is-approximated-below-supremum-modulus-family-ℝ μ ε =
    intro-exists
      ( modulus-supremum-modulus-family-ℝ μ ε)
      ( le-modulus-supremum-modulus-family-ℝ μ ε)

  is-supremum-supremum-modulus-family-ℝ :
    supremum-modulus-family-ℝ → is-supremum-family-ℝ y x
  is-supremum-supremum-modulus-family-ℝ μ =
    ( is-upper-bound-supremum-modulus-family-ℝ μ ,
      is-approximated-below-supremum-modulus-family-ℝ μ)
```

### The predicate of being a modulated supremum

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} (y : I → ℝ l2) (x : ℝ l3)
  where

  is-modulated-supremum-prop-family-ℝ : Prop (l1 ⊔ l2 ⊔ l3)
  is-modulated-supremum-prop-family-ℝ =
    ( is-upper-bound-prop-family-of-elements-Large-Poset ℝ-Large-Poset y x) ∧
    ( trunc-Prop ((ε : ℚ⁺) → Σ I (λ i → le-ℝ (x -ℝ real-ℚ⁺ ε) (y i))))

  is-modulated-supremum-family-ℝ : UU (l1 ⊔ l2 ⊔ l3)
  is-modulated-supremum-family-ℝ =
    type-Prop is-modulated-supremum-prop-family-ℝ

  is-supremum-is-modulated-supremum-family-ℝ :
    is-modulated-supremum-family-ℝ →
    is-supremum-family-ℝ y x
  is-supremum-is-modulated-supremum-family-ℝ (H , μ) =
    ( H ,
      rec-trunc-Prop
        ( Π-Prop ℚ⁺ (λ ε → ∃ I (λ i → le-prop-ℝ (x -ℝ real-ℚ⁺ ε) (y i))))
        ( map-Π (λ x → unit-trunc-Prop))
        ( μ))

  is-upper-bound-is-modulated-supremum-family-ℝ :
    is-modulated-supremum-family-ℝ →
    is-upper-bound-family-of-elements-Large-Poset ℝ-Large-Poset y x
  is-upper-bound-is-modulated-supremum-family-ℝ = pr1

  is-approximated-below-is-modulated-supremum-family-ℝ :
    is-modulated-supremum-family-ℝ →
    is-approximated-below-family-ℝ y x
  is-approximated-below-is-modulated-supremum-family-ℝ is-mod-sup-x =
    is-approximated-below-is-supremum-family-ℝ y x
      ( is-supremum-is-modulated-supremum-family-ℝ is-mod-sup-x)
```

### The type of modulated suprema

```agda
module _
  {l1 l2 : Level} (l3 : Level) {I : UU l1} (y : I → ℝ l2)
  where

  has-modulated-supremum-family-ℝ : UU (l1 ⊔ l2 ⊔ lsuc l3)
  has-modulated-supremum-family-ℝ =
    Σ (ℝ l3) (is-modulated-supremum-family-ℝ y)

  has-supremum-family-has-modulated-supremum-family-ℝ :
    has-modulated-supremum-family-ℝ → has-supremum-family-ℝ y l3
  has-supremum-family-has-modulated-supremum-family-ℝ =
    tot (is-supremum-is-modulated-supremum-family-ℝ y)
```

## Properties

### Modulated suprema are least upper bounds

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} (y : I → ℝ l2) (x : ℝ l3)
  (is-mod-sup-x : is-modulated-supremum-family-ℝ y x)
  where

  is-least-upper-bound-is-modulated-supremum-family-ℝ :
    is-least-upper-bound-family-of-elements-Large-Poset
      ( ℝ-Large-Poset)
      ( y)
      ( x)
  is-least-upper-bound-is-modulated-supremum-family-ℝ =
    is-least-upper-bound-is-supremum-family-ℝ
      ( y)
      ( x)
      ( is-supremum-is-modulated-supremum-family-ℝ y x is-mod-sup-x)

  le-supremum-iff-le-element-modulated-family-ℝ :
    {l4 : Level} → (z : ℝ l4) →
    (le-ℝ z x) ↔ (exists I (λ i → le-prop-ℝ z (y i)))
  le-supremum-iff-le-element-modulated-family-ℝ =
    le-supremum-iff-le-element-family-ℝ
      ( y)
      ( x)
      ( is-supremum-is-modulated-supremum-family-ℝ y x is-mod-sup-x)
```

### Modulated suprema are unique up to similarity

```agda
module _
  {l1 l2 : Level} {I : UU l1} (x : I → ℝ l2)
  where

  abstract
    sim-is-modulated-supremum-family-ℝ :
      {l3 : Level} (y : ℝ l3) → is-modulated-supremum-family-ℝ x y →
      {l4 : Level} (z : ℝ l4) → is-modulated-supremum-family-ℝ x z →
      sim-ℝ y z
    sim-is-modulated-supremum-family-ℝ y is-mod-sup-y z is-mod-sup-z =
      sim-is-supremum-family-ℝ
        ( x)
        ( y)
        ( is-supremum-is-modulated-supremum-family-ℝ x y is-mod-sup-y)
        ( z)
        ( is-supremum-is-modulated-supremum-family-ℝ x z is-mod-sup-z)
```

### Modulated suprema are unique

```agda
module _
  {l1 l2 : Level} (l3 : Level) {I : UU l1} (y : I → ℝ l2)
  where

  abstract
    is-prop-has-modulated-supremum-family-ℝ :
      is-prop (has-modulated-supremum-family-ℝ l3 y)
    is-prop-has-modulated-supremum-family-ℝ =
      is-prop-all-elements-equal
        ( λ (x₁ , is-mod-sup-x₁) (x₂ , is-mod-sup-x₂) →
          eq-type-subtype
            ( is-modulated-supremum-prop-family-ℝ y)
            ( eq-sim-ℝ
              ( sim-is-modulated-supremum-family-ℝ
                ( y)
                ( x₁)
                ( is-mod-sup-x₁)
                ( x₂)
                ( is-mod-sup-x₂))))

  has-modulated-supremum-prop-family-ℝ : Prop (l1 ⊔ l2 ⊔ lsuc l3)
  has-modulated-supremum-prop-family-ℝ =
    ( has-modulated-supremum-family-ℝ l3 y ,
      is-prop-has-modulated-supremum-family-ℝ)
```

### Assuming countable choice, suprema over sets are modulated suprema

```agda
module _
  {l1 l2 l3 : Level}
  (acℕ : level-ACℕ (l1 ⊔ l2 ⊔ l3))
  (I : Set l1) (y : type-Set I → ℝ l2) (x : ℝ l3)
  where

  is-modulated-supremum-is-supremum-family-ACℕ-ℝ :
    is-supremum-family-ℝ y x →
    is-modulated-supremum-family-ℝ y x
  is-modulated-supremum-is-supremum-family-ACℕ-ℝ is-sup-x =
    rec-trunc-Prop
      ( is-modulated-supremum-prop-family-ℝ y x)
      ( λ μ →
        ( is-upper-bound-is-supremum-family-ℝ y x is-sup-x ,
          unit-trunc-Prop μ))
      ( choice-countable-discrete-set-ACℕ
        ( set-ℚ⁺)
        ( is-countable-set-ℚ⁺)
        ( has-decidable-equality-ℚ⁺)
        ( acℕ)
        ( λ ε → Σ-Set I (λ i → set-Prop (le-prop-ℝ (x -ℝ real-ℚ⁺ ε) (y i))))
        ( is-approximated-below-is-supremum-family-ℝ y x is-sup-x))
```
