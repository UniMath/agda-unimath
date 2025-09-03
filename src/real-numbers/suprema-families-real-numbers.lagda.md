# Suprema of families of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.suprema-families-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.least-upper-bounds-large-posets
open import order-theory.upper-bounds-large-posets

open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.strict-inequality-real-numbers
open import real-numbers.subsets-real-numbers
```

</details>

## Idea

A [real number](real-numbers.dedekind-real-numbers.md) `x` is the
{{#concept "supremum" disambiguation="of a set of real numbers" Agda=is-supremum-family-ℝ WD="supremum" WDID=Q215071}}
of a family `y` of real numbers indexed by `I` if `x` is an
[upper bound](order-theory.upper-bounds-large-posets.md) of `y` in the
[large poset of real numbers](real-numbers.inequality-real-numbers.md) and `x`
is approximated below by the `yᵢ`: for all `ε : ℚ⁺`, there
[exists](foundation.existential-quantification.md) an `i : I` such that
`x - yᵢ < ε`.

Classically, suprema and
[least upper bounds](order-theory.least-upper-bounds-large-posets.md) are
equivalent, but constructively being a supremum is a stronger condition, often
required for constructive analysis.

## Definition

### Suprema of families of real numbers

```agda
module _
  {l1 l2 : Level} {I : UU l1} (y : I → ℝ l2)
  where

  is-approximated-below-prop-family-ℝ :
    {l3 : Level} → ℝ l3 → Prop (l1 ⊔ l2 ⊔ l3)
  is-approximated-below-prop-family-ℝ x =
    Π-Prop
      ( ℚ⁺)
      ( λ ε → ∃ I (λ i → le-prop-ℝ (x -ℝ real-ℚ⁺ ε) (y i)))

  is-approximated-below-family-ℝ : {l3 : Level} → ℝ l3 → UU (l1 ⊔ l2 ⊔ l3)
  is-approximated-below-family-ℝ x =
    type-Prop (is-approximated-below-prop-family-ℝ x)

  is-supremum-prop-family-ℝ : {l3 : Level} → ℝ l3 → Prop (l1 ⊔ l2 ⊔ l3)
  is-supremum-prop-family-ℝ x =
    is-upper-bound-prop-family-of-elements-Large-Poset
      ( ℝ-Large-Poset)
      ( y)
      ( x) ∧
    is-approximated-below-prop-family-ℝ x

  is-supremum-family-ℝ : {l3 : Level} → ℝ l3 → UU (l1 ⊔ l2 ⊔ l3)
  is-supremum-family-ℝ x = type-Prop (is-supremum-prop-family-ℝ x)

  is-upper-bound-is-supremum-family-ℝ :
    {l3 : Level} → (x : ℝ l3) → is-supremum-family-ℝ x →
    is-upper-bound-family-of-elements-Large-Poset ℝ-Large-Poset y x
  is-upper-bound-is-supremum-family-ℝ _ = pr1

  is-approximated-below-is-supremum-family-ℝ :
    {l3 : Level} → (x : ℝ l3) → is-supremum-family-ℝ x →
    is-approximated-below-family-ℝ x
  is-approximated-below-is-supremum-family-ℝ _ = pr2
```

### Suprema of subsets of real numbers

```agda
module _
  {l1 l2 : Level} (S : subset-ℝ l1 l2) where

  is-supremum-prop-subset-ℝ :
    {l3 : Level} → ℝ l3 → Prop (l1 ⊔ lsuc l2 ⊔ l3)
  is-supremum-prop-subset-ℝ =
    is-supremum-prop-family-ℝ (inclusion-subset-ℝ S)

  is-supremum-subset-ℝ : {l3 : Level} → ℝ l3 → UU (l1 ⊔ lsuc l2 ⊔ l3)
  is-supremum-subset-ℝ x = type-Prop (is-supremum-prop-subset-ℝ x)
```

## Properties

### A supremum is a least upper bound

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} (y : I → ℝ l2) (x : ℝ l3)
  (is-supremum-x-yᵢ : is-supremum-family-ℝ y x)
  where

  abstract
    is-least-upper-bound-is-supremum-family-ℝ :
      is-least-upper-bound-family-of-elements-Large-Poset
        ( ℝ-Large-Poset)
        ( y)
        ( x)
    pr1 (is-least-upper-bound-is-supremum-family-ℝ z) yᵢ≤z =
      leq-not-le-ℝ z x
        ( λ z<x →
          let open do-syntax-trunc-Prop empty-Prop
          in do
            (ε⁺@(ε , _) , ε<x-z) ←
              exists-ℚ⁺-in-lower-cut-ℝ⁺ (positive-diff-le-ℝ z x z<x)
            (i , x-ε<yᵢ) ←
              is-approximated-below-is-supremum-family-ℝ y x is-supremum-x-yᵢ ε⁺
            not-leq-le-ℝ z (y i)
              ( transitive-le-ℝ z (x -ℝ real-ℚ⁺ ε⁺) (y i)
                ( x-ε<yᵢ)
                ( le-transpose-left-add-ℝ' _ _ _
                  ( le-transpose-right-diff-ℝ _ _ _
                    ( le-real-is-in-lower-cut-ℚ ε (x -ℝ z) ε<x-z))))
              ( yᵢ≤z i))
    pr2 (is-least-upper-bound-is-supremum-family-ℝ z) x≤z i =
      transitive-leq-ℝ (y i) x z x≤z
        ( is-upper-bound-is-supremum-family-ℝ y x is-supremum-x-yᵢ i)
```

### Suprema are unique up to similarity

```agda
module _
  {l1 l2 : Level} {I : UU l1} (x : I → ℝ l2)
  where

  abstract
    sim-is-supremum-family-ℝ :
      {l3 : Level} (y : ℝ l3) → is-supremum-family-ℝ x y →
      {l4 : Level} (z : ℝ l4) → is-supremum-family-ℝ x z →
      sim-ℝ y z
    sim-is-supremum-family-ℝ y is-sup-y z is-sup-z =
      sim-sim-leq-ℝ
        ( sim-is-least-upper-bound-family-of-elements-Large-Poset ℝ-Large-Poset
          ( is-least-upper-bound-is-supremum-family-ℝ x y is-sup-y)
          ( is-least-upper-bound-is-supremum-family-ℝ x z is-sup-z))
```

### Having a supremum at a given universe level is a proposition

```agda
module _
  {l1 l2 : Level} {I : UU l1} (x : I → ℝ l2) (l3 : Level)
  where

  has-supremum-family-ℝ : UU (l1 ⊔ l2 ⊔ lsuc l3)
  has-supremum-family-ℝ = Σ (ℝ l3) (is-supremum-family-ℝ x)

  abstract
    is-prop-has-supremum-family-ℝ : is-prop has-supremum-family-ℝ
    is-prop-has-supremum-family-ℝ =
      is-prop-all-elements-equal
        ( λ (y , is-sup-y) (z , is-sup-z) →
          eq-type-subtype
            ( is-supremum-prop-family-ℝ x)
            ( eq-sim-ℝ (sim-is-supremum-family-ℝ x y is-sup-y z is-sup-z)))

  has-supremum-prop-family-ℝ : Prop (l1 ⊔ l2 ⊔ lsuc l3)
  has-supremum-prop-family-ℝ =
    ( has-supremum-family-ℝ , is-prop-has-supremum-family-ℝ)
```

### A real number `r` is less than the supremum of the `yᵢ` if and only if it is less than some `yᵢ`

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} (y : I → ℝ l2) (x : ℝ l3)
  (is-supremum-x-yᵢ : is-supremum-family-ℝ y x)
  where

  abstract
    le-supremum-le-element-family-ℝ :
      {l4 : Level} → (z : ℝ l4) (i : I) → le-ℝ z (y i) → le-ℝ z x
    le-supremum-le-element-family-ℝ z i z<yᵢ =
      concatenate-le-leq-ℝ z (y i) x z<yᵢ (pr1 is-supremum-x-yᵢ i)

    le-element-le-supremum-family-ℝ :
      {l4 : Level} → (z : ℝ l4) → le-ℝ z x → exists I (λ i → le-prop-ℝ z (y i))
    le-element-le-supremum-family-ℝ z z<x =
      let open do-syntax-trunc-Prop (∃ I (λ i → le-prop-ℝ z (y i)))
      in do
        (ε⁺@(ε , _) , ε<x-z) ←
          exists-ℚ⁺-in-lower-cut-ℝ⁺ (positive-diff-le-ℝ z x z<x)
        (i , x-ε<yᵢ) ←
          is-approximated-below-is-supremum-family-ℝ y x is-supremum-x-yᵢ ε⁺
        intro-exists
          ( i)
          ( transitive-le-ℝ z (x -ℝ real-ℚ ε) (y i)
            ( x-ε<yᵢ)
            ( le-transpose-left-add-ℝ' _ _ _
              ( le-transpose-right-diff-ℝ _ _ _
                ( le-real-is-in-lower-cut-ℚ ε (x -ℝ z) ε<x-z))))

    le-supremum-iff-le-element-family-ℝ :
      {l4 : Level} → (z : ℝ l4) →
      (le-ℝ z x) ↔ (exists I (λ i → le-prop-ℝ z (y i)))
    pr1 (le-supremum-iff-le-element-family-ℝ z) =
      le-element-le-supremum-family-ℝ z
    pr2 (le-supremum-iff-le-element-family-ℝ z) =
      elim-exists (le-prop-ℝ z x) (le-supremum-le-element-family-ℝ z)
```

## See also

- [Infima of families of real numbers](real-numbers.infima-families-real-numbers.md)

## External links

- [Suprema](https://ncatlab.org/nlab/show/join#constructive) at $n$Lab
