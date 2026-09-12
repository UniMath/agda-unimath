# Kleene's fixed point theorem for posets

```agda
module domain-theory.kleenes-fixed-point-theorem-posets where
```

<details><summary>Imports</summary>

```agda
open import domain-theory.omega-continuous-maps-posets
open import domain-theory.omega-iteration-fixed-point-construction-posets

open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.fixed-points-endofunctions
open import foundation.identity-types
open import foundation.iterating-functions
open import foundation.universe-levels

open import order-theory.bottom-elements-posets
open import order-theory.least-upper-bounds-posets
open import order-theory.order-preserving-maps-posets
open import order-theory.posets
open import order-theory.upper-bounds-posets
```

</details>

## Idea

{{#concept "Kleene's fixed point theorem" Disambiguation="posets" WD="Kleene fixed-point theorem" WDID=Q3527263}}
states that given an
[ω-continuous](domain-theory.omega-continuous-maps-posets.md) endomap
`f : 𝒜 → 𝒜` on a [poset](order-theory.posets.md) `𝒜`, then for every `x ∈ 𝒜`
such that `x ≤ f x`, the ω-transfinite application of `f` to `x`,`f^ω(x)`, if it
exists, is a [fixed point](foundation.fixed-points-endofunctions.md) of `f`:

```text
  x ≤ f(x) ≤ f²(x) ≤ … ≤ fⁿ(x) ≤ … ≤ f^ω(x) = f(^fω(x)) = ….
```

If `𝒜` has a [bottom element](order-theory.bottom-elements-posets.md) `⊥`, then
this construction applied to `⊥` gives a least fixed point of `f`.

We prove this theorem as a corollary of
[the ω-iteration fixed point construction for posets](domain-theory.omega-iteration-fixed-point-construction-posets.md).

## Construction

```agda
module _
  {l1 l2 : Level}
  (𝒜 : Poset l1 l2)
  {f : type-Poset 𝒜 → type-Poset 𝒜}
  (H : preserves-order-Poset 𝒜 𝒜 f)
  (x : type-Poset 𝒜)
  (p : leq-Poset 𝒜 x (f x))
  where

  leq-succ-family-of-elements-construction-kleene-hom-Poset :
    (n : ℕ) →
    leq-Poset 𝒜
      ( iterate n f x)
      ( iterate (succ-ℕ n) f x)
  leq-succ-family-of-elements-construction-kleene-hom-Poset zero-ℕ =
    p
  leq-succ-family-of-elements-construction-kleene-hom-Poset (succ-ℕ n) =
    H ( iterate n f x)
      ( iterate (succ-ℕ n) f x)
      ( leq-succ-family-of-elements-construction-kleene-hom-Poset n)

  family-of-elements-construction-kleene-hom-Poset : ℕ → type-Poset 𝒜
  family-of-elements-construction-kleene-hom-Poset =
    family-of-elements-construction-ω-iteration-Poset 𝒜 x
      leq-succ-family-of-elements-construction-kleene-hom-Poset

  hom-construction-kleene-hom-Poset :
    hom-Poset ℕ-Poset 𝒜
  hom-construction-kleene-hom-Poset =
    hom-construction-ω-iteration-Poset 𝒜 x
      leq-succ-family-of-elements-construction-kleene-hom-Poset
```

## Theorems

### Fixed point theorem for order preserving maps

```agda
module _
  {l1 l2 : Level}
  (𝒜 : Poset l1 l2)
  {f : type-Poset 𝒜 → type-Poset 𝒜}
  (H : preserves-order-Poset 𝒜 𝒜 f)
  (x : type-Poset 𝒜)
  (p : leq-Poset 𝒜 x (f x))
  (s :
    has-least-upper-bound-family-of-elements-Poset 𝒜
      ( family-of-elements-construction-kleene-hom-Poset 𝒜 H x p))
  (F :
    preserves-ω-supremum-Poset 𝒜 𝒜 f
      ( hom-construction-kleene-hom-Poset 𝒜 H x p))
  where

  point-construction-kleene-hom-Poset : type-Poset 𝒜
  point-construction-kleene-hom-Poset =
    point-construction-ω-iteration-Poset 𝒜 x
      ( leq-succ-family-of-elements-construction-kleene-hom-Poset 𝒜 H x p)
      ( s)
      ( F)

  is-fixed-point-construction-kleene-hom-Poset :
    f (point-construction-kleene-hom-Poset) ＝
    point-construction-kleene-hom-Poset
  is-fixed-point-construction-kleene-hom-Poset =
    is-fixed-point-construction-ω-iteration-Poset 𝒜 x
      ( leq-succ-family-of-elements-construction-kleene-hom-Poset 𝒜 H x p)
      ( s)
      ( F)

  fixed-point-construction-kleene-hom-Poset :
    fixed-point f
  fixed-point-construction-kleene-hom-Poset =
    fixed-point-construction-ω-iteration-Poset 𝒜 x
      ( leq-succ-family-of-elements-construction-kleene-hom-Poset 𝒜 H x p)
      ( s)
      ( F)

module _
  {l1 l2 : Level}
  (𝒜 : Poset l1 l2)
  {f : type-Poset 𝒜 → type-Poset 𝒜}
  (F : is-ω-continuous-Poset 𝒜 𝒜 f)
  (x : type-Poset 𝒜)
  (p : leq-Poset 𝒜 x (f x))
  where

  family-of-elements-construction-kleene-Poset : ℕ → type-Poset 𝒜
  family-of-elements-construction-kleene-Poset =
    family-of-elements-construction-kleene-hom-Poset 𝒜
      ( preserves-order-is-ω-continuous-Poset 𝒜 𝒜 F)
      ( x)
      ( p)

  hom-construction-kleene-Poset : hom-Poset ℕ-Poset 𝒜
  hom-construction-kleene-Poset =
    hom-construction-kleene-hom-Poset 𝒜
      ( preserves-order-is-ω-continuous-Poset 𝒜 𝒜 F)
      ( x)
      ( p)
```

### Fixed point theorem for ω-continuous maps

```agda
module _
  {l1 l2 : Level}
  (𝒜 : Poset l1 l2)
  {f : type-Poset 𝒜 → type-Poset 𝒜}
  (F : is-ω-continuous-Poset 𝒜 𝒜 f)
  (x : type-Poset 𝒜)
  (p : leq-Poset 𝒜 x (f x))
  (s :
    has-least-upper-bound-family-of-elements-Poset 𝒜
      ( family-of-elements-construction-kleene-Poset 𝒜 F x p))
  where

  point-construction-kleene-Poset : type-Poset 𝒜
  point-construction-kleene-Poset =
    point-construction-kleene-hom-Poset 𝒜
      ( preserves-order-is-ω-continuous-Poset 𝒜 𝒜 F)
      ( x)
      ( p)
      ( s)
      ( F (hom-construction-kleene-Poset 𝒜 F x p))

  is-fixed-point-construction-kleene-Poset :
    f (point-construction-kleene-Poset) ＝ point-construction-kleene-Poset
  is-fixed-point-construction-kleene-Poset =
    is-fixed-point-construction-kleene-hom-Poset 𝒜
      ( preserves-order-is-ω-continuous-Poset 𝒜 𝒜 F)
      ( x)
      ( p)
      ( s)
      ( F (hom-construction-kleene-Poset 𝒜 F x p))

  fixed-point-construction-kleene-Poset : fixed-point f
  fixed-point-construction-kleene-Poset =
    point-construction-kleene-Poset , is-fixed-point-construction-kleene-Poset
```

### Least fixed point theorem for order preserving maps

If `𝒜` has a bottom element, then Kleene's fixed point construction applied to
this element gives a least fixed point of `f`.

```agda
module _
  {l1 l2 : Level}
  (𝒜 : Poset l1 l2)
  {f : type-Poset 𝒜 → type-Poset 𝒜}
  (H : preserves-order-Poset 𝒜 𝒜 f)
  (b@(⊥ , b') : has-bottom-element-Poset 𝒜)
  (s :
    has-least-upper-bound-family-of-elements-Poset 𝒜
      ( family-of-elements-construction-kleene-hom-Poset 𝒜 H ⊥ (b' (f ⊥))))
  (F :
    preserves-ω-supremum-Poset 𝒜 𝒜 f
      ( hom-construction-kleene-hom-Poset 𝒜 H ⊥ (b' (f ⊥))))
  where

  point-theorem-kleene-hom-Poset : type-Poset 𝒜
  point-theorem-kleene-hom-Poset =
    point-construction-kleene-hom-Poset 𝒜 H ⊥ (b' (f ⊥)) s F

  fixed-point-theorem-kleene-hom-Poset : fixed-point f
  fixed-point-theorem-kleene-hom-Poset =
    fixed-point-construction-kleene-hom-Poset 𝒜 H ⊥ (b' (f ⊥)) s F

  is-upper-bound-family-of-elements-is-fixed-point-theorem-kleene-hom-Poset :
    {z : type-Poset 𝒜} → f z ＝ z →
    is-upper-bound-family-of-elements-Poset 𝒜
      ( family-of-elements-construction-kleene-hom-Poset 𝒜 H ⊥ (b' (f ⊥)))
      ( z)
  is-upper-bound-family-of-elements-is-fixed-point-theorem-kleene-hom-Poset
    { z} q zero-ℕ =
    b' z
  is-upper-bound-family-of-elements-is-fixed-point-theorem-kleene-hom-Poset
    {z} q (succ-ℕ n) =
    concatenate-leq-eq-Poset 𝒜
      ( H ( iterate n f ⊥)
          ( z)
          ( is-upper-bound-family-of-elements-is-fixed-point-theorem-kleene-hom-Poset
            ( q)
            ( n)))
      ( q)

  is-least-fixed-point-theorem-kleene-hom-Poset :
    (q : fixed-point f) → leq-Poset 𝒜 point-theorem-kleene-hom-Poset (pr1 q)
  is-least-fixed-point-theorem-kleene-hom-Poset (z , q) =
    pr1
      ( pr2 s z)
      ( is-upper-bound-family-of-elements-is-fixed-point-theorem-kleene-hom-Poset
        ( q))
```

### Least fixed point theorem for ω-continuous maps

If `𝒜` has a bottom element, then Kleene's fixed point construction applied to
this element gives a least fixed point of `f`.

```agda
module _
  {l1 l2 : Level}
  (𝒜 : Poset l1 l2)
  {f : type-Poset 𝒜 → type-Poset 𝒜}
  (F : is-ω-continuous-Poset 𝒜 𝒜 f)
  (b@(⊥ , b') : has-bottom-element-Poset 𝒜)
  (s :
    has-least-upper-bound-family-of-elements-Poset 𝒜
      ( family-of-elements-construction-kleene-Poset 𝒜 F ⊥ (b' (f ⊥))))
  where

  point-theorem-kleene-Poset : type-Poset 𝒜
  point-theorem-kleene-Poset =
    point-construction-kleene-Poset 𝒜 F ⊥ (b' (f ⊥)) s

  fixed-point-theorem-kleene-Poset : fixed-point f
  fixed-point-theorem-kleene-Poset =
    fixed-point-construction-kleene-Poset 𝒜 F ⊥ (b' (f ⊥)) s

  is-least-fixed-point-theorem-kleene-Poset :
    (q : fixed-point f) → leq-Poset 𝒜 point-theorem-kleene-Poset (pr1 q)
  is-least-fixed-point-theorem-kleene-Poset =
    is-least-fixed-point-theorem-kleene-hom-Poset 𝒜
      ( preserves-order-is-ω-continuous-Poset 𝒜 𝒜 F)
      ( b)
      ( s)
      ( F (hom-construction-kleene-Poset 𝒜 F ⊥ (b' (f ⊥))))
```

## External links

- [Kleene fixed-point theorem](https://en.wikipedia.org/wiki/Kleene_fixed-point_theorem)
  at Wikipedia
- [Kleene's fixed point theorem](https://ncatlab.org/nlab/show/Kleene%27s+fixed+point+theorem)
  at $n$Lab
