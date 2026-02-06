# The ω-iteration fixed point construction for posets

```agda
module domain-theory.omega-iteration-fixed-point-construction-posets where
```

<details><summary>Imports</summary>

```agda
open import domain-theory.omega-continuous-maps-posets

open import elementary-number-theory.decidable-total-order-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.fixed-points-endofunctions
open import foundation.function-types
open import foundation.identity-types
open import foundation.iterating-functions
open import foundation.universe-levels

open import order-theory.inflationary-maps-posets
open import order-theory.increasing-sequences-posets
open import order-theory.least-upper-bounds-posets
open import order-theory.order-preserving-maps-posets
open import order-theory.posets
open import order-theory.upper-bounds-posets
```

</details>

## Idea

Given a map `f : 𝒜 → 𝒜` on a [poset](order-theory.posets.md) and `x : 𝒜` such
that the [sequence](lists.sequences.md) of
[iterates](foundation.iterating-functions.md) `x ≤ f x ≤ f² x ≤ ⋯` is
increasing, has a
[least upper bound](order-theory.least-upper-bounds-posets.md), and `f`
preserves that least upper bound. Then that least upper bound is a
[fixed point](foundation.fixed-points-endofunctions.md) of `f`.

## Construction

```agda
module _
  {l1 l2 : Level}
  (𝒜 : Poset l1 l2)
  {f : type-Poset 𝒜 → type-Poset 𝒜}
  (x : type-Poset 𝒜)
  (p : (n : ℕ) → leq-Poset 𝒜 (iterate n f x) (iterate (succ-ℕ n) f x))
  where

  family-of-elements-construction-ω-iteration-Poset :
    ℕ → type-Poset 𝒜
  family-of-elements-construction-ω-iteration-Poset n =
    iterate n f x

  leq-succ-family-of-elements-construction-ω-iteration-Poset :
    (n : ℕ) →
    leq-Poset 𝒜
      ( family-of-elements-construction-ω-iteration-Poset n)
      ( family-of-elements-construction-ω-iteration-Poset (succ-ℕ n))
  leq-succ-family-of-elements-construction-ω-iteration-Poset = p

  hom-construction-ω-iteration-Poset :
    hom-Poset ℕ-Poset 𝒜
  hom-construction-ω-iteration-Poset =
    hom-ind-ℕ-Poset 𝒜
      ( family-of-elements-construction-ω-iteration-Poset)
      ( leq-succ-family-of-elements-construction-ω-iteration-Poset)

module _
  {l1 l2 : Level}
  (𝒜 : Poset l1 l2)
  {f : type-Poset 𝒜 → type-Poset 𝒜}
  (x : type-Poset 𝒜)
  (p : (n : ℕ) → leq-Poset 𝒜 (iterate n f x) (iterate (succ-ℕ n) f x))
  (s :
    has-least-upper-bound-family-of-elements-Poset 𝒜
      ( family-of-elements-construction-ω-iteration-Poset 𝒜 x p))
  (F :
    preserves-ω-supremum-Poset 𝒜 𝒜 f
      ( hom-construction-ω-iteration-Poset 𝒜 x p))
  where

  point-construction-ω-iteration-Poset : type-Poset 𝒜
  point-construction-ω-iteration-Poset = pr1 s

  is-upper-bound-shifted-family-of-elements-construction-ω-iteration-Poset :
    is-upper-bound-family-of-elements-Poset 𝒜
      ( f ∘ family-of-elements-construction-ω-iteration-Poset 𝒜 x p)
      ( f point-construction-ω-iteration-Poset)
  is-upper-bound-shifted-family-of-elements-construction-ω-iteration-Poset =
    is-upper-bound-is-least-upper-bound-family-of-elements-Poset 𝒜 (F s)

  is-upper-bound-family-of-elements-map-point-construction-ω-iteration-Poset :
    is-upper-bound-family-of-elements-Poset 𝒜
      ( family-of-elements-construction-ω-iteration-Poset 𝒜 x p)
      ( f point-construction-ω-iteration-Poset)
  is-upper-bound-family-of-elements-map-point-construction-ω-iteration-Poset
    zero-ℕ =
    transitive-leq-Poset 𝒜 x
      ( f x)
      ( f point-construction-ω-iteration-Poset)
      ( is-upper-bound-shifted-family-of-elements-construction-ω-iteration-Poset
        ( zero-ℕ))
      ( p zero-ℕ)
  is-upper-bound-family-of-elements-map-point-construction-ω-iteration-Poset
    (succ-ℕ n) =
    is-upper-bound-shifted-family-of-elements-construction-ω-iteration-Poset n

  leq-point-construction-ω-iteration-Poset :
    leq-Poset 𝒜
      ( point-construction-ω-iteration-Poset)
      ( f point-construction-ω-iteration-Poset)
  leq-point-construction-ω-iteration-Poset =
    pr1
      ( pr2 s (f point-construction-ω-iteration-Poset))
      ( is-upper-bound-family-of-elements-map-point-construction-ω-iteration-Poset)

  geq-point-construction-ω-iteration-Poset :
    leq-Poset 𝒜
      ( f point-construction-ω-iteration-Poset)
      ( point-construction-ω-iteration-Poset)
  geq-point-construction-ω-iteration-Poset =
    pr1
      ( F s point-construction-ω-iteration-Poset)
      ( is-upper-bound-is-least-upper-bound-family-of-elements-Poset 𝒜 (pr2 s) ∘
        succ-ℕ)

  is-fixed-point-construction-ω-iteration-Poset :
    f point-construction-ω-iteration-Poset ＝
    point-construction-ω-iteration-Poset
  is-fixed-point-construction-ω-iteration-Poset =
    antisymmetric-leq-Poset 𝒜
      ( f point-construction-ω-iteration-Poset)
      ( point-construction-ω-iteration-Poset)
      ( geq-point-construction-ω-iteration-Poset)
      ( leq-point-construction-ω-iteration-Poset)

  fixed-point-construction-ω-iteration-Poset :
    fixed-point f
  fixed-point-construction-ω-iteration-Poset =
    ( point-construction-ω-iteration-Poset ,
      is-fixed-point-construction-ω-iteration-Poset)
```

## See also

- [Kleene's fixed point theorem for posets](domain-theory.keenes-fixed-point-theorem-posets.md)
- [Kleene's fixed point theorem for ω-complete posets](domain-theory.keenes-fixed-point-theorem-omega-complete-posets.md)
