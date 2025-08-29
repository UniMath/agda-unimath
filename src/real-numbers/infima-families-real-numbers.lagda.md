# Infima of families of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.infima-families-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.binary-transport
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import logic.functoriality-existential-quantification

open import order-theory.greatest-lower-bounds-large-posets
open import order-theory.lower-bounds-large-posets
open import order-theory.upper-bounds-large-posets

open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.strict-inequality-real-numbers
open import real-numbers.subsets-real-numbers
open import real-numbers.suprema-families-real-numbers
```

</details>

## Idea

A [real number](real-numbers.dedekind-real-numbers.md) `x` is the
{{#concept "infimum" disambiguation="of a set of real numbers" Agda=is-infimum-family-ℝ WD="infimum" WDID=Q1199948}}
of a family `y` of real numbers indexed by `I` if `x` is a
[lower bound](order-theory.lower-bounds-large-posets.md) of `y` in the
[large poset of real numbers](real-numbers.inequality-real-numbers.md) and `x`
is approximated above by the `yᵢ`: for all `ε : ℚ⁺`, there
[exists](foundation.existential-quantification.md) an `i : I` such that
`yᵢ < x + ε`.

Classically, infima and
[greatest lower bounds](order-theory.greatest-lower-bounds-large-posets.md) are
equivalent, but constructively being an infimum is a stronger condition, often
required for constructive analysis.

## Definition

### Infima of families of real numbers

```agda
module _
  {l1 l2 : Level} {I : UU l1} (y : I → ℝ l2)
  where

  is-approximated-above-prop-family-ℝ :
    {l3 : Level} → ℝ l3 → Prop (l1 ⊔ l2 ⊔ l3)
  is-approximated-above-prop-family-ℝ x =
    Π-Prop
      ( ℚ⁺)
      ( λ ε → ∃ I (λ i → le-ℝ-Prop (y i) (x +ℝ real-ℚ⁺ ε)))

  is-approximated-above-family-ℝ : {l3 : Level} → ℝ l3 → UU (l1 ⊔ l2 ⊔ l3)
  is-approximated-above-family-ℝ x =
    type-Prop (is-approximated-above-prop-family-ℝ x)

  is-infimum-prop-family-ℝ : {l3 : Level} → ℝ l3 → Prop (l1 ⊔ l2 ⊔ l3)
  is-infimum-prop-family-ℝ x =
    is-lower-bound-prop-family-of-elements-Large-Poset
      ( ℝ-Large-Poset)
      ( y)
      ( x) ∧
    is-approximated-above-prop-family-ℝ x

  is-infimum-family-ℝ : {l3 : Level} → ℝ l3 → UU (l1 ⊔ l2 ⊔ l3)
  is-infimum-family-ℝ x = type-Prop (is-infimum-prop-family-ℝ x)

  is-lower-bound-is-infimum-family-ℝ :
    {l3 : Level} → (x : ℝ l3) → is-infimum-family-ℝ x →
    is-lower-bound-family-of-elements-Large-Poset ℝ-Large-Poset y x
  is-lower-bound-is-infimum-family-ℝ _ = pr1

  is-approximated-above-is-infimum-family-ℝ :
    {l3 : Level} → (x : ℝ l3) → is-infimum-family-ℝ x →
    is-approximated-above-family-ℝ x
  is-approximated-above-is-infimum-family-ℝ _ = pr2
```

### Infima of subsets of real numbers

```agda
module _
  {l1 l2 : Level} (S : subset-ℝ l1 l2) where

  is-infimum-prop-subset-ℝ :
    {l3 : Level} → ℝ l3 → Prop (l1 ⊔ lsuc l2 ⊔ l3)
  is-infimum-prop-subset-ℝ =
    is-infimum-prop-family-ℝ (inclusion-subset-ℝ S)

  is-infimum-subset-ℝ : {l3 : Level} → ℝ l3 → UU (l1 ⊔ lsuc l2 ⊔ l3)
  is-infimum-subset-ℝ x = type-Prop (is-infimum-prop-subset-ℝ x)
```

## Properties

### A infimum is a greatest lower bound

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} (y : I → ℝ l2) (x : ℝ l3)
  (is-infimum-x-yᵢ : is-infimum-family-ℝ y x)
  where

  abstract
    is-greatest-lower-bound-is-infimum-family-ℝ :
      is-greatest-lower-bound-family-of-elements-Large-Poset
        ( ℝ-Large-Poset)
        ( y)
        ( x)
    pr1 (is-greatest-lower-bound-is-infimum-family-ℝ z) z≤yᵢ =
      leq-not-le-ℝ x z
        ( λ x<z →
          let open do-syntax-trunc-Prop empty-Prop
          in do
            (ε⁺@(ε , _) , ε<z-x) ←
              exists-ℚ⁺-in-lower-cut-ℝ⁺ (positive-diff-le-ℝ x z x<z)
            (i , yᵢ<x+ε) ←
              is-approximated-above-is-infimum-family-ℝ y x is-infimum-x-yᵢ ε⁺
            not-leq-le-ℝ (y i) z
              ( transitive-le-ℝ (y i) (x +ℝ real-ℚ ε) z
                ( le-transpose-right-diff-ℝ' _ z _
                  ( le-real-is-in-lower-cut-ℚ ε (z -ℝ x) ε<z-x))
                ( yᵢ<x+ε))
              ( z≤yᵢ i))
    pr2 (is-greatest-lower-bound-is-infimum-family-ℝ z) z≤x i =
      transitive-leq-ℝ z x (y i)
        ( is-lower-bound-is-infimum-family-ℝ y x is-infimum-x-yᵢ i)
        ( z≤x)
```

### Infima are unique up to similarity

```agda
module _
  {l1 l2 : Level} {I : UU l1} (x : I → ℝ l2)
  where

  abstract
    sim-is-infimum-family-ℝ :
      {l3 : Level} (y : ℝ l3) → is-infimum-family-ℝ x y →
      {l4 : Level} (z : ℝ l4) → is-infimum-family-ℝ x z →
      sim-ℝ y z
    sim-is-infimum-family-ℝ y is-inf-y z is-inf-z =
      sim-sim-leq-ℝ
        ( sim-is-greatest-lower-bound-family-of-elements-Large-Poset
          ( ℝ-Large-Poset)
          ( is-greatest-lower-bound-is-infimum-family-ℝ x y is-inf-y)
          ( is-greatest-lower-bound-is-infimum-family-ℝ x z is-inf-z))
```

### Having an infimum at a given universe level is a proposition

```agda
module _
  {l1 l2 : Level} {I : UU l1} (x : I → ℝ l2) (l3 : Level)
  where

  has-infimum-family-ℝ : UU (l1 ⊔ l2 ⊔ lsuc l3)
  has-infimum-family-ℝ = Σ (ℝ l3) (is-infimum-family-ℝ x)

  abstract
    is-prop-has-infimum-family-ℝ : is-prop has-infimum-family-ℝ
    is-prop-has-infimum-family-ℝ =
      is-prop-all-elements-equal
        ( λ (y , is-inf-y) (z , is-inf-z) →
          eq-type-subtype
            ( is-infimum-prop-family-ℝ x)
            ( eq-sim-ℝ (sim-is-infimum-family-ℝ x y is-inf-y z is-inf-z)))

  has-infimum-prop-family-ℝ : Prop (l1 ⊔ l2 ⊔ lsuc l3)
  has-infimum-prop-family-ℝ =
    ( has-infimum-family-ℝ , is-prop-has-infimum-family-ℝ)
```

### A real number `r` is greater than the infimum of the `yᵢ` if and only if it is greater than some `yᵢ`

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} (y : I → ℝ l2) (x : ℝ l3)
  (is-infimum-x-yᵢ : is-infimum-family-ℝ y x)
  where

  le-infimum-le-element-family-ℝ :
    {l4 : Level} → (z : ℝ l4) (i : I) → le-ℝ (y i) z → le-ℝ x z
  le-infimum-le-element-family-ℝ z i =
    concatenate-leq-le-ℝ x (y i) z
      ( is-lower-bound-is-infimum-family-ℝ y x is-infimum-x-yᵢ i)

  le-element-le-infimum-family-ℝ :
    {l4 : Level} → (z : ℝ l4) → le-ℝ x z → exists I (λ i → le-ℝ-Prop (y i) z)
  le-element-le-infimum-family-ℝ z x<z =
    let open do-syntax-trunc-Prop (∃ I (λ i → le-ℝ-Prop (y i) z))
    in do
      (ε⁺@(ε , _) , ε<z-x) ←
        exists-ℚ⁺-in-lower-cut-ℝ⁺ (positive-diff-le-ℝ x z x<z)
      (i , yᵢ<x+ε) ←
        is-approximated-above-is-infimum-family-ℝ y x is-infimum-x-yᵢ ε⁺
      intro-exists
        ( i)
        ( transitive-le-ℝ (y i) (x +ℝ real-ℚ ε) z
          ( le-transpose-right-diff-ℝ' _ z _
            ( le-real-is-in-lower-cut-ℚ ε (z -ℝ x) ε<z-x))
          ( yᵢ<x+ε))

  le-infimum-iff-le-element-family-ℝ :
    {l4 : Level} → (z : ℝ l4) →
    (le-ℝ x z) ↔ (exists I (λ i → le-ℝ-Prop (y i) z))
  pr1 (le-infimum-iff-le-element-family-ℝ z) =
    le-element-le-infimum-family-ℝ z
  pr2 (le-infimum-iff-le-element-family-ℝ z) =
    elim-exists (le-ℝ-Prop x z) (le-infimum-le-element-family-ℝ z)
```

### The infimum of a family of real numbers is the negation of the supremum of the negation of the family

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} (y : I → ℝ l2) (x : ℝ l3)
  (is-supremum-x-neg-yᵢ : is-supremum-family-ℝ (neg-ℝ ∘ y) x)
  where

  abstract
    is-lower-bound-neg-supremum-neg-family-ℝ :
      is-lower-bound-family-of-elements-Large-Poset ℝ-Large-Poset y (neg-ℝ x)
    is-lower-bound-neg-supremum-neg-family-ℝ i =
      tr
        ( leq-ℝ (neg-ℝ x))
        ( neg-neg-ℝ (y i))
        ( neg-leq-ℝ _ _
          ( is-upper-bound-is-supremum-family-ℝ
            ( neg-ℝ ∘ y)
            ( x)
            ( is-supremum-x-neg-yᵢ)
            ( i)))

    is-approximated-above-neg-supremum-neg-family-ℝ :
      is-approximated-above-family-ℝ y (neg-ℝ x)
    is-approximated-above-neg-supremum-neg-family-ℝ ε =
      map-tot-exists
        ( λ i x-ε<-yᵢ →
          binary-tr le-ℝ
            ( neg-neg-ℝ _)
            ( distributive-neg-diff-ℝ _ _ ∙ commutative-add-ℝ _ _)
            ( neg-le-ℝ (x -ℝ real-ℚ⁺ ε) (neg-ℝ (y i)) x-ε<-yᵢ))
        ( is-approximated-below-is-supremum-family-ℝ
          ( neg-ℝ ∘ y)
          ( x)
          ( is-supremum-x-neg-yᵢ)
          ( ε))

    is-infimum-neg-supremum-neg-family-ℝ : is-infimum-family-ℝ y (neg-ℝ x)
    is-infimum-neg-supremum-neg-family-ℝ =
      ( is-lower-bound-neg-supremum-neg-family-ℝ ,
        is-approximated-above-neg-supremum-neg-family-ℝ)
```

### The supremum of a family of real numbers is the negation of the infimum of the negation of the family

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} (y : I → ℝ l2) (x : ℝ l3)
  (is-infimum-x-neg-yᵢ : is-infimum-family-ℝ (neg-ℝ ∘ y) x)
  where

  abstract
    is-upper-bound-neg-infimum-neg-family-ℝ :
      is-upper-bound-family-of-elements-Large-Poset ℝ-Large-Poset y (neg-ℝ x)
    is-upper-bound-neg-infimum-neg-family-ℝ i =
      tr
        ( λ w → leq-ℝ w (neg-ℝ x))
        ( neg-neg-ℝ (y i))
        ( neg-leq-ℝ _ _
          ( is-lower-bound-is-infimum-family-ℝ
            ( neg-ℝ ∘ y)
            ( x)
            ( is-infimum-x-neg-yᵢ)
            ( i)))

    is-approximated-below-neg-infimum-neg-family-ℝ :
      is-approximated-below-family-ℝ y (neg-ℝ x)
    is-approximated-below-neg-infimum-neg-family-ℝ ε =
      map-tot-exists
        ( λ i -yᵢ<x+ε →
          binary-tr le-ℝ
            ( distributive-neg-add-ℝ _ _)
            ( neg-neg-ℝ (y i))
            ( neg-le-ℝ (neg-ℝ (y i)) (x +ℝ real-ℚ⁺ ε) -yᵢ<x+ε))
        ( is-approximated-above-is-infimum-family-ℝ
          ( neg-ℝ ∘ y)
          ( x)
          ( is-infimum-x-neg-yᵢ)
          ( ε))

    is-supremum-neg-infimum-neg-family-ℝ : is-supremum-family-ℝ y (neg-ℝ x)
    is-supremum-neg-infimum-neg-family-ℝ =
      ( is-upper-bound-neg-infimum-neg-family-ℝ ,
        is-approximated-below-neg-infimum-neg-family-ℝ)
```

## See also

- [Suprema of families of real numbers](real-numbers.suprema-families-real-numbers.md)
- [Infima](https://ncatlab.org/nlab/show/join#constructive) at $n$Lab
