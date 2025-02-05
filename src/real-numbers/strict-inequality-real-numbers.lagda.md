# Strict inequality of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.strict-inequality-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.conjunction
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.negation
open import foundation.propositions
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
```

</details>

## Idea

```agda
module _
  {l1 l2 : Level}
  (x : ℝ l1)
  (y : ℝ l2)
  where

  le-ℝ-Prop : Prop (l1 ⊔ l2)
  le-ℝ-Prop = ∃ ℚ (λ q → upper-cut-ℝ x q ∧ lower-cut-ℝ y q)

  le-ℝ : UU (l1 ⊔ l2)
  le-ℝ = type-Prop le-ℝ-Prop

  is-prop-le-ℝ : is-prop le-ℝ
  is-prop-le-ℝ = is-prop-type-Prop le-ℝ-Prop
```

## Properties

### Strict inequality on the reals is irreflexive

```agda
module _
  {l : Level}
  (x : ℝ l)
  where

  irreflexive-le-ℝ : ¬ (le-ℝ x x)
  irreflexive-le-ℝ =
    elim-exists
      ( empty-Prop)
      λ q (q-in-ux , q-in-lx) → is-disjoint-cut-ℝ x q (q-in-lx , q-in-ux)
```

### Strict inequality on the reals is asymmetric

```agda
module _
  {l1 l2 : Level}
  (x : ℝ l1)
  (y : ℝ l2)
  where

  asymmetric-le-ℝ : le-ℝ x y → ¬ (le-ℝ y x)
  asymmetric-le-ℝ x<y y<x =
    elim-exists
      ( empty-Prop)
      ( λ p (p-in-ux , p-in-ly) →
        elim-exists
          ( empty-Prop)
          ( λ q (q-in-uy , q-in-lx) →
            rec-coproduct
              ( λ p<q →
                asymmetric-le-ℚ
                  ( p)
                  ( q)
                  ( p<q)
                  ( le-lower-upper-cut-ℝ x q p q-in-lx p-in-ux))
              ( λ q≤p →
                not-leq-le-ℚ
                  ( p)
                  ( q)
                  ( le-lower-upper-cut-ℝ y p q p-in-ly q-in-uy)
                  ( q≤p))
              ( decide-le-leq-ℚ p q))
          ( y<x))
      ( x<y)
```

### Strict inequality on the reals is transitive

```agda
module _
  {l1 l2 l3 : Level}
  (x : ℝ l1)
  (y : ℝ l2)
  (z : ℝ l3)
  where

  transitive-le-ℝ : le-ℝ y z → le-ℝ x y → le-ℝ x z
  transitive-le-ℝ y<z =
    elim-exists
      (le-ℝ-Prop x z)
      (λ p (p-in-ux , p-in-ly) →
        elim-exists
          (le-ℝ-Prop x z)
          (λ q (q-in-uy , q-in-lz) →
            intro-exists
              p
              ( p-in-ux ,
                le-lower-cut-ℝ
                  ( z)
                  ( p)
                  ( q)
                  ( le-lower-upper-cut-ℝ y p q p-in-ly q-in-uy)
                  ( q-in-lz)))
          ( y<z))
