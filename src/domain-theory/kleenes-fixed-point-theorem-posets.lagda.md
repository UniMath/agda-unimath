# Kleene's fixed point theorem for posets

```agda
module domain-theory.kleenes-fixed-point-theorem-posets where
```

<details><summary>Imports</summary>

```agda
open import domain-theory.directed-families-posets
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

{{#concept "Kleene's fixed point theorem" Disambiguation="posets" WD="Kleene fixed-point theorem" WDID=Q3527263}}
states that given an [ω-continuous](domain-theory.ω-continuous-maps-posets.md)
endomap `f : 𝒜 → 𝒜` on a [poset](domain-theory.posets.md) `𝒜`, then for every
`x ∈ 𝒜` such that `x ≤ f x`, the ω-transfinite application of `f` to `x`, given
that it exists, is a [fixed point](foundation.fixed-points-endofunctions.md) of
`f`:

```text
  x ≤ f(x) ≤ f²(x) ≤ … ≤ fⁿ(x) ≤ … ≤ fω(x) = f(fω(x)) = ….
```

If `𝒜` has a [bottom element](order-theory.bottom-elements-posets.md) `⊥`, then
this construction gives a least fixed point of `f`.

## Theorem

### Kleene's fixed point construction on posets

```agda
module _
  {l1 l2 : Level}
  (𝒜 : Poset l1 l2)
  {f : type-Poset 𝒜 → type-Poset 𝒜}
  (F : is-ω-continuous-Poset 𝒜 𝒜 f)
  (x : type-Poset 𝒜)
  (p : leq-Poset 𝒜 x (f x))
  where

  family-of-elements-kleene-Poset : ℕ → type-Poset 𝒜
  family-of-elements-kleene-Poset n = iterate n f x

  leq-succ-family-of-elements-kleene-Poset :
    (n : ℕ) →
    leq-Poset 𝒜
      ( family-of-elements-kleene-Poset n)
      ( family-of-elements-kleene-Poset (succ-ℕ n))
  leq-succ-family-of-elements-kleene-Poset zero-ℕ = p
  leq-succ-family-of-elements-kleene-Poset (succ-ℕ n) =
    preserves-order-is-ω-continuous-Poset 𝒜 𝒜 F
      ( family-of-elements-kleene-Poset n)
      ( family-of-elements-kleene-Poset (succ-ℕ n))
      ( leq-succ-family-of-elements-kleene-Poset n)

  hom-kleene-Poset : hom-Poset ℕ-Poset 𝒜
  hom-kleene-Poset =
    hom-ind-ℕ-Poset 𝒜
      ( family-of-elements-kleene-Poset)
      ( leq-succ-family-of-elements-kleene-Poset)

module _
  {l1 l2 : Level}
  (𝒜 : Poset l1 l2)
  {f : type-Poset 𝒜 → type-Poset 𝒜}
  (F : is-ω-continuous-Poset 𝒜 𝒜 f)
  (x : type-Poset 𝒜)
  (p : leq-Poset 𝒜 x (f x))
  (s :
    has-least-upper-bound-family-of-elements-Poset 𝒜
      ( family-of-elements-kleene-Poset 𝒜 F x p))
  where

  point-kleene-Poset : type-Poset 𝒜
  point-kleene-Poset = pr1 s

  is-upper-bound-map-point-kleene-Poset :
    is-upper-bound-family-of-elements-Poset 𝒜
      ( family-of-elements-kleene-Poset 𝒜 F x p)
      ( f point-kleene-Poset)
  is-upper-bound-map-point-kleene-Poset zero-ℕ =
    transitive-leq-Poset 𝒜 x (f x)
      ( f point-kleene-Poset)
      ( preserves-order-is-ω-continuous-Poset 𝒜 𝒜 F x
        ( point-kleene-Poset)
        ( is-upper-bound-is-least-upper-bound-family-of-elements-Poset 𝒜
          ( pr2 s)
          ( 0)))
      ( p)
  is-upper-bound-map-point-kleene-Poset (succ-ℕ n) =
    preserves-order-is-ω-continuous-Poset 𝒜 𝒜 F
      ( family-of-elements-kleene-Poset 𝒜 F x p n)
      ( point-kleene-Poset)
      ( is-upper-bound-is-least-upper-bound-family-of-elements-Poset 𝒜
        ( pr2 s)
        ( n))

  leq-point-kleene-Poset :
    leq-Poset 𝒜 (point-kleene-Poset) (f point-kleene-Poset)
  leq-point-kleene-Poset =
    pr1 (pr2 s (f point-kleene-Poset)) (is-upper-bound-map-point-kleene-Poset)

  geq-point-kleene-Poset :
    leq-Poset 𝒜 (f point-kleene-Poset) (point-kleene-Poset)
  geq-point-kleene-Poset =
    pr1
      ( F (hom-kleene-Poset 𝒜 F x p) s point-kleene-Poset)
      ( is-upper-bound-is-least-upper-bound-family-of-elements-Poset 𝒜 (pr2 s) ∘
        succ-ℕ)

  is-fixed-point-kleene-Poset : f (point-kleene-Poset) ＝ point-kleene-Poset
  is-fixed-point-kleene-Poset =
    antisymmetric-leq-Poset 𝒜
      ( f (point-kleene-Poset))
      ( point-kleene-Poset)
      ( geq-point-kleene-Poset)
      ( leq-point-kleene-Poset)

  fixed-point-kleene-Poset : fixed-point f
  fixed-point-kleene-Poset =
    point-kleene-Poset , is-fixed-point-kleene-Poset
```

### Kleene's least fixed point theorem for posets with a bottom element

If `𝒜` has a bottom element, then Kleene's fixed point construction gives a
least fixed point of `f`.

```agda
module _
  {l1 l2 : Level}
  (𝒜 : Poset l1 l2)
  {f : type-Poset 𝒜 → type-Poset 𝒜}
  (F : is-ω-continuous-Poset 𝒜 𝒜 f)
  (b : has-bottom-element-Poset 𝒜)
  (s :
    has-least-upper-bound-family-of-elements-Poset 𝒜
      ( family-of-elements-kleene-Poset 𝒜 F (pr1 b) (pr2 b (f (pr1 b)))))
  where
```

## External links

- [Kleene fixed-point theorem](https://en.wikipedia.org/wiki/Kleene_fixed-point_theorem)
  at Wikipedia
- [Kleene's fixed point theorem](https://ncatlab.org/nlab/show/Kleene%27s+fixed+point+theorem)
  at $n$Lab
