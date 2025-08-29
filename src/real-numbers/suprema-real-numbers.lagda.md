# Suprema of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.suprema-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.strict-inequality-real-numbers
open import foundation.empty-types
open import foundation.dependent-pair-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.conjunction
open import foundation.propositional-truncations
open import foundation.universe-levels
open import foundation.existential-quantification
open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-real-numbers
open import order-theory.upper-bounds-large-posets
open import order-theory.least-upper-bounds-large-posets
```

</details>

## Idea

A [real number](real-numbers.dedekind-real-numbers.md) `x` is the
{{#concept "supremum" disambiguation="of a set of real numbers" Agda=is-supremum-family-ℝ WD="supremum" WDID=Q215071}}
of a family `y` of real numbers indexed by `I` if `x` is an
[upper bound](order-theory.upper-bounds-large-posets.md) of `y` in the
[large poset of real numbers](real-numbers.inequality-real-numbers.md) and
`x` is approximated below by the `yᵢ`: for all `ε : ℚ⁺`, there
[exists](foundation.existential-quantification.md) an `i : I` such that
`x - yᵢ < ε`.

Classically, suprema and
[least upper bounds](order-theory.least-upper-bounds-large-posets.md) are
equivalent, but constructively being a supremum is a stronger condition.

## Definition

```agda
module _
  {l1 l2 : Level} {I : UU l1} (y : I → ℝ l2)
  where

  is-approximated-below-prop-family-ℝ :
    {l3 : Level} → ℝ l3 → Prop (l1 ⊔ l2 ⊔ l3)
  is-approximated-below-prop-family-ℝ x =
    Π-Prop
      ( ℚ⁺)
      ( λ ε → ∃ I (λ i → le-ℝ-Prop (x -ℝ real-ℚ⁺ ε) (y i)))

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

## Properties

### A supremum is a least upper bound

```agda
module _
  {l1 l2 l3 l4 : Level} {I : UU l1} (y : I → ℝ l2) (x : ℝ l3)
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

### A real number `r` is less than the supremum of the `yᵢ` if and only if it is less than some `yᵢ`

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} (y : I → ℝ l2) (x : ℝ l3)
  (is-supremum-x-yᵢ : is-supremum-family-ℝ y x)
  where

  le-supremum-le-element-family-ℝ :
    {l4 : Level} → (z : ℝ l4) (i : I) → le-ℝ z (y i) → le-ℝ z x
  le-supremum-le-element-family-ℝ z i z<yᵢ =
    concatenate-le-leq-ℝ z (y i) x z<yᵢ (pr1 is-supremum-x-yᵢ i)

  le-element-le-supremum-family-ℝ :
    {l4 : Level} → (z : ℝ l4) → le-ℝ z x → exists I (λ i → le-ℝ-Prop z (y i))
  le-element-le-supremum-family-ℝ z z<x =
    let open do-syntax-trunc-Prop (∃ I (λ i → le-ℝ-Prop z (y i)))
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
    (le-ℝ z x) ↔ (exists I (λ i → le-ℝ-Prop z (y i)))
  pr1 (le-supremum-iff-le-element-family-ℝ z) =
    le-element-le-supremum-family-ℝ z
  pr2 (le-supremum-iff-le-element-family-ℝ z) =
    elim-exists (le-ℝ-Prop z x) (le-supremum-le-element-family-ℝ z)
```

## See also

* [Suprema](https://ncatlab.org/nlab/show/join#constructive) at $n$Lab
