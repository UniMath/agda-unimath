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
open import foundation.disjunction
open import foundation.double-negation
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.rational-real-numbers
```

</details>

## Idea

The
{{#concept "standard strict ordering" Disambiguation="real numbers" Agda=le-ℝ}}
on the [real numbers](real-numbers.dedekind-real-numbers.md) is defined as the
presence of a [rational number](elementary-number-theory.rational-numbers.md)
between them. This is the definition used in {{#cite UF13}}, section 11.2.1.

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
      ( λ q (q-in-ux , q-in-lx) → is-disjoint-cut-ℝ x q (q-in-lx , q-in-ux))
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
      ( le-ℝ-Prop x z)
      ( λ p (p-in-ux , p-in-ly) →
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
```

### The canonical map from rationals to reals preserves strict inequality

```agda
preserves-le-real-ℚ : (x y : ℚ) → le-ℚ x y → le-ℝ (real-ℚ x) (real-ℚ y)
preserves-le-real-ℚ x y x<y =
  intro-exists
    ( mediant-ℚ x y)
    ( le-left-mediant-ℚ x y x<y , le-right-mediant-ℚ x y x<y)
```

### The reals have no lower or upper bound

```agda
module _
  {l : Level}
  (x : ℝ l)
  where

  exists-lesser-ℝ : exists (ℝ lzero) (λ y → le-ℝ-Prop y x)
  exists-lesser-ℝ =
    elim-exists
      ( ∃ (ℝ lzero) (λ y → le-ℝ-Prop y x))
      ( λ q q-in-lx →
        intro-exists
          ( real-ℚ q)
          ( forward-implication (is-rounded-lower-cut-ℝ x q) q-in-lx))
      ( is-inhabited-lower-cut-ℝ x)

  exists-greater-ℝ : exists (ℝ lzero) (λ y → le-ℝ-Prop x y)
  exists-greater-ℝ =
    elim-exists
      ( ∃ (ℝ lzero) (λ y → le-ℝ-Prop x y))
      ( λ q q-in-ux →
        intro-exists
          ( real-ℚ q)
          ( elim-exists
              ( le-ℝ-Prop x (real-ℚ q))
              ( λ r (r<q , r-in-ux) → intro-exists r (r-in-ux , r<q))
              ( forward-implication (is-rounded-upper-cut-ℝ x q) q-in-ux)))
      ( is-inhabited-upper-cut-ℝ x)
```

### Negation reverses the strict ordering of real numbers

```agda
module _
  {l1 l2 : Level}
  (x : ℝ l1)
  (y : ℝ l2)
  where

  reverses-order-neg-ℝ : le-ℝ x y → le-ℝ (neg-ℝ y) (neg-ℝ x)
  reverses-order-neg-ℝ =
    elim-exists
      ( le-ℝ-Prop (neg-ℝ y) (neg-ℝ x))
      ( λ p (p-in-ux , p-in-ly) →
        intro-exists
          ( neg-ℚ p)
          ( tr (is-in-lower-cut-ℝ y) (inv (neg-neg-ℚ p)) p-in-ly ,
            tr (is-in-upper-cut-ℝ x) (inv (neg-neg-ℚ p)) p-in-ux))
```

### Relationships between inequality, strict inequality, and their negations

```agda
module _
  {l1 l2 : Level}
  (x : ℝ l1)
  (y : ℝ l2)
  where

  not-leq-le-ℝ : le-ℝ x y → ¬ (leq-ℝ y x)
  not-leq-le-ℝ x<y y≤x =
    elim-exists
      ( empty-Prop)
      ( λ q (q-in-ux , q-in-ly) →
        is-disjoint-cut-ℝ x q (y≤x q q-in-ly , q-in-ux))
      ( x<y)

  leq-not-le-ℝ : ¬ (le-ℝ x y) → leq-ℝ y x
  leq-not-le-ℝ x≮y p p∈ly =
    elim-exists
      ( lower-cut-ℝ x p)
      ( λ q (p<q , q∈ly) →
        elim-disjunction
          ( lower-cut-ℝ x p)
          ( id)
          ( λ q∈ux → ex-falso (x≮y (intro-exists q (q∈ux , q∈ly))))
          ( is-located-lower-upper-cut-ℝ x p q p<q))
      ( forward-implication (is-rounded-lower-cut-ℝ y p) p∈ly)

module _
  {l1 l2 : Level}
  (x : ℝ l1)
  (y : ℝ l2)
  where

  not-le-leq-ℝ : leq-ℝ x y → ¬ (le-ℝ y x)
  not-le-leq-ℝ x≤y y<x = not-leq-le-ℝ y x y<x x≤y

  leq-iff-not-le-ℝ : leq-ℝ x y ↔ ¬ (le-ℝ y x)
  pr1 leq-iff-not-le-ℝ = not-le-leq-ℝ
  pr2 leq-iff-not-le-ℝ = leq-not-le-ℝ y x
```

## References

{­{#bibliography}}
