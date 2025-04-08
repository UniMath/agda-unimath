# The maximum of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.maximum-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import metric-spaces.metric-space-functions-metric-spaces
open import metric-spaces.short-functions-metric-spaces

open import order-theory.large-join-semilattices
open import order-theory.least-upper-bounds-large-posets

open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.lower-dedekind-real-numbers
open import real-numbers.maximum-lower-dedekind-real-numbers
open import real-numbers.maximum-upper-dedekind-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.strict-inequality-real-numbers
open import real-numbers.upper-dedekind-real-numbers
```

</details>

## Idea

The
{{#concept "maximum" Disambiguation="binary, Dedekind real numbers" Agda=binary-max-ℝ WD="maximum" WDID=Q10578722}}
of two [Dedekind real numbers](real-numbers.dedekind-real-numbers.md) `x` and
`y` is a Dedekind real number with lower cut equal to the union of `x` and `y`'s
lower cuts, and upper cut equal to the intersection of their upper cuts.

## Definition

```agda
module _
  {l1 l2 : Level}
  (x : ℝ l1) (y : ℝ l2)
  where

  lower-real-binary-max-ℝ : lower-ℝ (l1 ⊔ l2)
  lower-real-binary-max-ℝ = binary-max-lower-ℝ (lower-real-ℝ x) (lower-real-ℝ y)

  upper-real-binary-max-ℝ : upper-ℝ (l1 ⊔ l2)
  upper-real-binary-max-ℝ = binary-max-upper-ℝ (upper-real-ℝ x) (upper-real-ℝ y)

  abstract
    is-disjoint-lower-upper-binary-max-ℝ :
      is-disjoint-lower-upper-ℝ lower-real-binary-max-ℝ upper-real-binary-max-ℝ
    is-disjoint-lower-upper-binary-max-ℝ q (q<x∨q<y , x<q , y<q) =
      elim-disjunction
        ( empty-Prop)
        ( λ q<x → is-disjoint-cut-ℝ x q (q<x , x<q))
        ( λ q<y → is-disjoint-cut-ℝ y q (q<y , y<q))
        ( q<x∨q<y)

    is-located-lower-upper-binary-max-ℝ :
      is-located-lower-upper-ℝ lower-real-binary-max-ℝ upper-real-binary-max-ℝ
    is-located-lower-upper-binary-max-ℝ p q p<q =
      elim-disjunction
        ( claim)
        ( λ p<x → inl-disjunction (inl-disjunction p<x))
        ( λ x<q →
          elim-disjunction
            ( claim)
            ( λ p<y → inl-disjunction (inr-disjunction p<y))
            ( λ y<q → inr-disjunction (x<q , y<q))
            ( is-located-lower-upper-cut-ℝ y p q p<q))
        ( is-located-lower-upper-cut-ℝ x p q p<q)
      where
        claim : Prop (l1 ⊔ l2)
        claim =
          cut-lower-ℝ lower-real-binary-max-ℝ p ∨
          cut-upper-ℝ upper-real-binary-max-ℝ q

  binary-max-ℝ : ℝ (l1 ⊔ l2)
  binary-max-ℝ =
    real-lower-upper-ℝ
      ( lower-real-binary-max-ℝ)
      ( upper-real-binary-max-ℝ)
      ( is-disjoint-lower-upper-binary-max-ℝ)
      ( is-located-lower-upper-binary-max-ℝ)
```

## Properties

### The binary maximum is a least upper bound

```agda
module _
  {l1 l2 : Level}
  (x : ℝ l1) (y : ℝ l2)
  where

  is-least-binary-upper-bound-binary-max-ℝ :
    is-least-binary-upper-bound-Large-Poset
      ( ℝ-Large-Poset)
      ( x)
      ( y)
      ( binary-max-ℝ x y)
  is-least-binary-upper-bound-binary-max-ℝ z =
    is-least-binary-upper-bound-binary-max-lower-ℝ
      ( lower-real-ℝ x)
      ( lower-real-ℝ y)
      ( lower-real-ℝ z)
```

### The binary maximum is a binary upper bound

```agda
module _
  {l1 l2 : Level}
  (x : ℝ l1) (y : ℝ l2)
  where

  abstract
    leq-left-binary-max-ℝ : leq-ℝ x (binary-max-ℝ x y)
    leq-left-binary-max-ℝ =
      pr1
        ( is-binary-upper-bound-is-least-binary-upper-bound-Large-Poset
          ( ℝ-Large-Poset)
          ( x)
          ( y)
          ( is-least-binary-upper-bound-binary-max-ℝ x y))

    leq-right-binary-max-ℝ : leq-ℝ y (binary-max-ℝ x y)
    leq-right-binary-max-ℝ =
      pr2
        ( is-binary-upper-bound-is-least-binary-upper-bound-Large-Poset
          ( ℝ-Large-Poset)
          ( x)
          ( y)
          ( is-least-binary-upper-bound-binary-max-ℝ x y))
```

### The binary maximum is commutative

```agda
module _
  {l1 l2 : Level}
  (x : ℝ l1) (y : ℝ l2)
  where

  opaque
    unfolding sim-ℝ

    commutative-binary-max-ℝ : binary-max-ℝ x y ＝ binary-max-ℝ y x
    commutative-binary-max-ℝ =
      eq-sim-ℝ
        ( sim-is-least-binary-upper-bound-Large-Poset
          ( ℝ-Large-Poset)
          ( x)
          ( y)
          ( is-least-binary-upper-bound-binary-max-ℝ x y)
          ( is-binary-least-upper-bound-swap-Large-Poset
            ( ℝ-Large-Poset)
            ( y)
            ( x)
            ( binary-max-ℝ y x)
            ( is-least-binary-upper-bound-binary-max-ℝ y x)))
```

### The large poset of real numbers has joins

```agda
has-joins-ℝ-Large-Poset : has-joins-Large-Poset ℝ-Large-Poset
join-has-joins-Large-Poset has-joins-ℝ-Large-Poset = binary-max-ℝ
is-least-binary-upper-bound-join-has-joins-Large-Poset
  has-joins-ℝ-Large-Poset = is-least-binary-upper-bound-binary-max-ℝ
```

### The binary maximum preserves lower neighborhoods

```agda
module _
  {l1 l2 l3 : Level} (d : ℚ⁺)
  (x : ℝ l1) (y : ℝ l2) (z : ℝ l3)
  where

  preserves-lower-neighborhood-leq-left-binary-max-ℝ :
    leq-ℝ y (z +ℝ real-ℚ (rational-ℚ⁺ d)) →
    leq-ℝ
      ( binary-max-ℝ x y)
      ( (binary-max-ℝ x z) +ℝ real-ℚ (rational-ℚ⁺ d))
  preserves-lower-neighborhood-leq-left-binary-max-ℝ z≤y+d =
    leq-is-least-binary-upper-bound-Large-Poset
      ( ℝ-Large-Poset)
      ( x)
      ( y)
      ( is-least-binary-upper-bound-binary-max-ℝ x y)
      ( (binary-max-ℝ x z) +ℝ real-ℚ (rational-ℚ⁺ d))
      ( ( transitive-leq-ℝ
          ( x)
          ( binary-max-ℝ x z)
          ( binary-max-ℝ x z +ℝ real-ℚ (rational-ℚ⁺ d))
          ( leq-le-ℝ
            ( binary-max-ℝ x z)
            ( binary-max-ℝ x z +ℝ real-ℚ (rational-ℚ⁺ d))
            ( le-left-add-real-ℝ⁺
              ( binary-max-ℝ x z)
              ( positive-real-ℚ⁺ d)))
          ( leq-left-binary-max-ℝ x z)) ,
        ( transitive-leq-ℝ
          ( y)
          ( z +ℝ real-ℚ (rational-ℚ⁺ d))
          ( binary-max-ℝ x z +ℝ real-ℚ (rational-ℚ⁺ d))
          ( preserves-leq-right-add-ℝ
            ( real-ℚ (rational-ℚ⁺ d))
            ( z)
            ( binary-max-ℝ x z)
            ( leq-right-binary-max-ℝ x z))
          ( z≤y+d)))

  preserves-lower-neighborhood-leq-right-binary-max-ℝ :
    leq-ℝ y (z +ℝ real-ℚ (rational-ℚ⁺ d)) →
    leq-ℝ
      ( binary-max-ℝ y x)
      ( (binary-max-ℝ z x) +ℝ real-ℚ (rational-ℚ⁺ d))
  preserves-lower-neighborhood-leq-right-binary-max-ℝ z≤y+d =
    binary-tr
      ( λ u v → leq-ℝ u (v +ℝ real-ℚ (rational-ℚ⁺ d)))
      ( commutative-binary-max-ℝ x y)
      ( commutative-binary-max-ℝ x z)
      ( preserves-lower-neighborhood-leq-left-binary-max-ℝ z≤y+d)
```

### The maximum with a real number is a short function `ℝ → ℝ`

```agda
module _
  {l1 l2 : Level} (x : ℝ l1)
  where

  is-short-function-left-binary-max-ℝ :
    is-short-function-Metric-Space
      ( metric-space-leq-ℝ l2)
      ( metric-space-leq-ℝ (l1 ⊔ l2))
      ( binary-max-ℝ x)
  is-short-function-left-binary-max-ℝ d y z Nyz =
    neighborhood-real-bound-each-leq-ℝ
      ( d)
      ( binary-max-ℝ x y)
      ( binary-max-ℝ x z)
      ( preserves-lower-neighborhood-leq-left-binary-max-ℝ d x y z
        ( left-real-bound-neighborhood-leq-ℝ d y z Nyz))
      ( preserves-lower-neighborhood-leq-left-binary-max-ℝ d x z y
        ( right-real-bound-neighborhood-leq-ℝ d y z Nyz))

  short-left-binary-max-ℝ :
    short-function-Metric-Space
      ( metric-space-leq-ℝ l2)
      ( metric-space-leq-ℝ (l1 ⊔ l2))
  short-left-binary-max-ℝ =
    binary-max-ℝ x , is-short-function-left-binary-max-ℝ
```

### The binary maximum is a short function from `ℝ` to the metric space of short functions `ℝ → ℝ`

```agda
module _
  {l1 l2 : Level}
  where

  is-short-function-short-left-binary-max-ℝ :
    is-short-function-Metric-Space
      ( metric-space-leq-ℝ l1)
      ( metric-space-short-function-Metric-Space
        ( metric-space-leq-ℝ l2)
        ( metric-space-leq-ℝ (l1 ⊔ l2)))
      ( short-left-binary-max-ℝ)
  is-short-function-short-left-binary-max-ℝ d x y Nxy z =
    neighborhood-real-bound-each-leq-ℝ
      ( d)
      ( binary-max-ℝ x z)
      ( binary-max-ℝ y z)
      ( preserves-lower-neighborhood-leq-right-binary-max-ℝ d z x y
        ( left-real-bound-neighborhood-leq-ℝ d x y Nxy))
      ( preserves-lower-neighborhood-leq-right-binary-max-ℝ d z y x
        ( right-real-bound-neighborhood-leq-ℝ d x y Nxy))

  short-binary-max-ℝ :
    short-function-Metric-Space
      ( metric-space-leq-ℝ l1)
      ( metric-space-short-function-Metric-Space
        ( metric-space-leq-ℝ l2)
        ( metric-space-leq-ℝ (l1 ⊔ l2)))
  short-binary-max-ℝ =
    short-left-binary-max-ℝ , is-short-function-short-left-binary-max-ℝ
```
