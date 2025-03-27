# The maximum of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.maximum-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.large-join-semilattices
open import order-theory.least-upper-bounds-large-posets

open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.lower-dedekind-real-numbers
open import real-numbers.maximum-lower-dedekind-real-numbers
open import real-numbers.maximum-upper-dedekind-real-numbers
open import real-numbers.similarity-real-numbers
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

  abstract
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
