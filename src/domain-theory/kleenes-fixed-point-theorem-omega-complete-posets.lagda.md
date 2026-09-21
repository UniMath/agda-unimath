# Kleene's fixed point theorem for ω-complete posets

```agda
module domain-theory.kleenes-fixed-point-theorem-omega-complete-posets where
```

<details><summary>Imports</summary>

```agda
open import domain-theory.directed-families-posets
open import domain-theory.kleenes-fixed-point-theorem-posets
open import domain-theory.omega-complete-posets
open import domain-theory.omega-continuous-maps-omega-complete-posets
open import domain-theory.omega-continuous-maps-posets

open import elementary-number-theory.decidable-total-order-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.fixed-points-endofunctions
open import foundation.function-types
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.iterating-functions
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.universe-levels

open import order-theory.bottom-elements-posets
open import order-theory.chains-posets
open import order-theory.inflattices
open import order-theory.inhabited-chains-posets
open import order-theory.least-upper-bounds-posets
open import order-theory.order-preserving-maps-posets
open import order-theory.posets
open import order-theory.suplattices
open import order-theory.upper-bounds-posets
```

</details>

## Idea

{{#concept "Kleene's fixed point theorem" Disambiguation="ω-complete posets" WD="Kleene fixed-point theorem" WDID=Q3527263}}
states that given an
[ω-continuous](domain-theory.omega-continuous-maps-omega-complete-posets.md)
endomap `f : 𝒜 → 𝒜` on an
[ω-complete poset](domain-theory.omega-complete-posets.md) `𝒜`, then for every
`x ∈ 𝒜` such that `x ≤ f x`, the ω-transfinite application of `f` to `x`,
`f^ω(x)`, which exists by ω-completeness, is a
[fixed point](foundation.fixed-points-endofunctions.md) of `f`:

```text
  x ≤ f(x) ≤ f²(x) ≤ … ≤ fⁿ(x) ≤ … ≤ f^ω(x) = f(f^ω(x)) = ….
```

If `𝒜` has a [bottom element](order-theory.bottom-elements-posets.md) `⊥`, then
this construction applied to `⊥` gives a least fixed point of `f`.

## Construction

```agda
module _
  {l1 l2 : Level}
  (𝒜 : ω-Complete-Poset l1 l2)
  {f : type-ω-Complete-Poset 𝒜 → type-ω-Complete-Poset 𝒜}
  (H :
    preserves-order-Poset
      ( poset-ω-Complete-Poset 𝒜)
      ( poset-ω-Complete-Poset 𝒜)
      ( f))
  (x : type-ω-Complete-Poset 𝒜)
  (p : leq-ω-Complete-Poset 𝒜 x (f x))
  where

  family-of-elements-construction-kleene-hom-ω-Complete-Poset :
    ℕ → type-ω-Complete-Poset 𝒜
  family-of-elements-construction-kleene-hom-ω-Complete-Poset =
    family-of-elements-construction-kleene-hom-Poset
      ( poset-ω-Complete-Poset 𝒜) H x p

  leq-succ-family-of-elements-construction-kleene-hom-ω-Complete-Poset :
    (n : ℕ) →
    leq-ω-Complete-Poset 𝒜
      ( family-of-elements-construction-kleene-hom-ω-Complete-Poset n)
      ( family-of-elements-construction-kleene-hom-ω-Complete-Poset (succ-ℕ n))
  leq-succ-family-of-elements-construction-kleene-hom-ω-Complete-Poset =
    leq-succ-family-of-elements-construction-kleene-hom-Poset
      ( poset-ω-Complete-Poset 𝒜) H x p

  hom-construction-kleene-hom-ω-Complete-Poset :
    hom-Poset ℕ-Poset (poset-ω-Complete-Poset 𝒜)
  hom-construction-kleene-hom-ω-Complete-Poset =
    hom-construction-kleene-hom-Poset (poset-ω-Complete-Poset 𝒜) H x p
```

## Theorems

### Fixed point theorem for order preserving maps

```agda
module _
  {l1 l2 : Level}
  (𝒜 : ω-Complete-Poset l1 l2)
  {f : type-ω-Complete-Poset 𝒜 → type-ω-Complete-Poset 𝒜}
  (H :
    preserves-order-Poset
      ( poset-ω-Complete-Poset 𝒜)
      ( poset-ω-Complete-Poset 𝒜)
      ( f))
  (x : type-ω-Complete-Poset 𝒜)
  (p : leq-ω-Complete-Poset 𝒜 x (f x))
  (F :
    preserves-ω-supremum-ω-Complete-Poset 𝒜 𝒜 f
      ( hom-construction-kleene-hom-ω-Complete-Poset 𝒜 H x p))
  where

  point-construction-kleene-hom-ω-Complete-Poset : type-ω-Complete-Poset 𝒜
  point-construction-kleene-hom-ω-Complete-Poset =
    point-construction-kleene-hom-Poset
      ( poset-ω-Complete-Poset 𝒜)
      ( H)
      ( x)
      ( p)
      ( is-ω-complete-ω-Complete-Poset 𝒜
        ( hom-construction-kleene-hom-ω-Complete-Poset 𝒜 H x p))
      ( F)

  is-fixed-point-construction-kleene-hom-ω-Complete-Poset :
    f (point-construction-kleene-hom-ω-Complete-Poset) ＝
    point-construction-kleene-hom-ω-Complete-Poset
  is-fixed-point-construction-kleene-hom-ω-Complete-Poset =
    is-fixed-point-construction-kleene-hom-Poset
      ( poset-ω-Complete-Poset 𝒜)
      ( H)
      ( x)
      ( p)
      ( is-ω-complete-ω-Complete-Poset 𝒜
        ( hom-construction-kleene-hom-ω-Complete-Poset 𝒜 H x p))
      ( F)

  fixed-point-construction-kleene-hom-ω-Complete-Poset :
    fixed-point f
  fixed-point-construction-kleene-hom-ω-Complete-Poset =
    ( point-construction-kleene-hom-ω-Complete-Poset ,
      is-fixed-point-construction-kleene-hom-ω-Complete-Poset)
```

### Fixed point theorem for ω-continuous maps

```agda
module _
  {l1 l2 : Level}
  (𝒜 : ω-Complete-Poset l1 l2)
  {f : type-ω-Complete-Poset 𝒜 → type-ω-Complete-Poset 𝒜}
  (F : is-ω-continuous-ω-Complete-Poset 𝒜 𝒜 f)
  (x : type-ω-Complete-Poset 𝒜)
  (p : leq-ω-Complete-Poset 𝒜 x (f x))
  where

  family-of-elements-construction-kleene-ω-Complete-Poset :
    ℕ → type-ω-Complete-Poset 𝒜
  family-of-elements-construction-kleene-ω-Complete-Poset =
    family-of-elements-construction-kleene-hom-ω-Complete-Poset 𝒜
      ( preserves-order-is-ω-continuous-ω-Complete-Poset 𝒜 𝒜 F)
      ( x)
      ( p)

  hom-construction-kleene-ω-Complete-Poset :
    hom-Poset ℕ-Poset (poset-ω-Complete-Poset 𝒜)
  hom-construction-kleene-ω-Complete-Poset =
    hom-construction-kleene-hom-ω-Complete-Poset 𝒜
      ( preserves-order-is-ω-continuous-ω-Complete-Poset 𝒜 𝒜 F)
      ( x)
      ( p)

module _
  {l1 l2 : Level}
  (𝒜 : ω-Complete-Poset l1 l2)
  {f : type-ω-Complete-Poset 𝒜 → type-ω-Complete-Poset 𝒜}
  (F : is-ω-continuous-ω-Complete-Poset 𝒜 𝒜 f)
  (x : type-ω-Complete-Poset 𝒜)
  (p : leq-ω-Complete-Poset 𝒜 x (f x))
  where

  point-construction-kleene-ω-Complete-Poset : type-ω-Complete-Poset 𝒜
  point-construction-kleene-ω-Complete-Poset =
    point-construction-kleene-hom-ω-Complete-Poset 𝒜
      ( preserves-order-is-ω-continuous-ω-Complete-Poset 𝒜 𝒜 F)
      ( x)
      ( p)
      ( F (hom-construction-kleene-ω-Complete-Poset 𝒜 F x p))

  is-fixed-point-construction-kleene-ω-Complete-Poset :
    f ( point-construction-kleene-ω-Complete-Poset) ＝
    point-construction-kleene-ω-Complete-Poset
  is-fixed-point-construction-kleene-ω-Complete-Poset =
    is-fixed-point-construction-kleene-hom-ω-Complete-Poset 𝒜
      ( preserves-order-is-ω-continuous-ω-Complete-Poset 𝒜 𝒜 F)
      ( x)
      ( p)
      ( F (hom-construction-kleene-ω-Complete-Poset 𝒜 F x p))

  fixed-point-construction-kleene-ω-Complete-Poset : fixed-point f
  fixed-point-construction-kleene-ω-Complete-Poset =
    point-construction-kleene-ω-Complete-Poset ,
    is-fixed-point-construction-kleene-ω-Complete-Poset
```

### Least fixed point theorem for order preserving maps

If `𝒜` has a bottom element, then Kleene's fixed point construction gives a
least fixed point of any order preserving endomap `f`.

```agda
module _
  {l1 l2 : Level}
  (𝒜 : ω-Complete-Poset l1 l2)
  {f : type-ω-Complete-Poset 𝒜 → type-ω-Complete-Poset 𝒜}
  (H :
    preserves-order-Poset
      ( poset-ω-Complete-Poset 𝒜)
      ( poset-ω-Complete-Poset 𝒜)
      ( f))
  (b@(⊥ , b') : has-bottom-element-Poset (poset-ω-Complete-Poset 𝒜))
  (F :
    preserves-ω-supremum-ω-Complete-Poset 𝒜 𝒜 f
      ( hom-construction-kleene-hom-ω-Complete-Poset 𝒜 H ⊥ (b' (f ⊥))))
  where

  point-theorem-kleene-hom-ω-Complete-Poset : type-ω-Complete-Poset 𝒜
  point-theorem-kleene-hom-ω-Complete-Poset =
    point-construction-kleene-hom-ω-Complete-Poset 𝒜 H ⊥ (b' (f ⊥)) F

  fixed-point-theorem-kleene-hom-ω-Complete-Poset : fixed-point f
  fixed-point-theorem-kleene-hom-ω-Complete-Poset =
    fixed-point-construction-kleene-hom-ω-Complete-Poset 𝒜 H ⊥ (b' (f ⊥)) F

  is-upper-bound-family-of-elements-is-fixed-point-theorem-kleene-hom-ω-Complete-Poset :
    {z : type-ω-Complete-Poset 𝒜} → f z ＝ z →
    is-upper-bound-family-of-elements-Poset (poset-ω-Complete-Poset 𝒜)
      ( family-of-elements-construction-kleene-hom-ω-Complete-Poset 𝒜 H
        ( ⊥)
        ( b' (f ⊥)))
      ( z)
  is-upper-bound-family-of-elements-is-fixed-point-theorem-kleene-hom-ω-Complete-Poset =
    is-upper-bound-family-of-elements-is-fixed-point-theorem-kleene-hom-Poset
      ( poset-ω-Complete-Poset 𝒜)
      ( H)
      ( b)
      ( is-ω-complete-ω-Complete-Poset 𝒜
        ( hom-construction-kleene-hom-ω-Complete-Poset 𝒜 H ⊥ (b' (f ⊥))))
      ( F)

  is-least-fixed-point-theorem-kleene-hom-ω-Complete-Poset :
    (q : fixed-point f) →
    leq-ω-Complete-Poset 𝒜 point-theorem-kleene-hom-ω-Complete-Poset (pr1 q)
  is-least-fixed-point-theorem-kleene-hom-ω-Complete-Poset =
    is-least-fixed-point-theorem-kleene-hom-Poset
      ( poset-ω-Complete-Poset 𝒜)
      ( H)
      ( b)
      ( is-ω-complete-ω-Complete-Poset 𝒜
        ( hom-construction-kleene-hom-ω-Complete-Poset 𝒜 H ⊥ (b' (f ⊥))))
      ( F)
```

### Least fixed point theorem for ω-continuous maps

If `𝒜` has a bottom element, then Kleene's fixed point construction gives a
least fixed point of any ω-continuous endomap `f`.

```agda
module _
  {l1 l2 : Level}
  (𝒜 : ω-Complete-Poset l1 l2)
  {f : type-ω-Complete-Poset 𝒜 → type-ω-Complete-Poset 𝒜}
  (F : is-ω-continuous-ω-Complete-Poset 𝒜 𝒜 f)
  (b@(⊥ , b') : has-bottom-element-Poset (poset-ω-Complete-Poset 𝒜))
  where

  point-theorem-kleene-ω-Complete-Poset : type-ω-Complete-Poset 𝒜
  point-theorem-kleene-ω-Complete-Poset =
    point-construction-kleene-ω-Complete-Poset 𝒜 F ⊥ (b' (f ⊥))

  fixed-point-theorem-kleene-ω-Complete-Poset : fixed-point f
  fixed-point-theorem-kleene-ω-Complete-Poset =
    fixed-point-construction-kleene-ω-Complete-Poset 𝒜 F ⊥ (b' (f ⊥))

  is-least-fixed-point-theorem-kleene-ω-Complete-Poset :
    (q : fixed-point f) →
    leq-ω-Complete-Poset 𝒜 point-theorem-kleene-ω-Complete-Poset (pr1 q)
  is-least-fixed-point-theorem-kleene-ω-Complete-Poset =
    is-least-fixed-point-theorem-kleene-hom-ω-Complete-Poset 𝒜
      ( preserves-order-is-ω-continuous-ω-Complete-Poset 𝒜 𝒜 F)
      ( b)
      ( F (hom-construction-kleene-ω-Complete-Poset 𝒜 F ⊥ (b' (f ⊥))))
```

## External links

- [Kleene fixed-point theorem](https://en.wikipedia.org/wiki/Kleene_fixed-point_theorem)
  at Wikipedia
- [Kleene's fixed point theorem](https://ncatlab.org/nlab/show/Kleene%27s+fixed+point+theorem)
  at $n$Lab
