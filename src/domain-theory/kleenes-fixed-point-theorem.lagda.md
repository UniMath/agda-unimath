# Kleene's fixed point theorem

```agda
module domain-theory.kleenes-fixed-point-theorem where
```

<details><summary>Imports</summary>

```agda
open import domain-theory.directed-complete-posets
open import domain-theory.directed-families-posets
open import domain-theory.scott-continuous-maps-posets

open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.fixed-points-endofunctions
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.iterating-functions
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.universe-levels

open import order-theory.bottom-elements-posets
open import order-theory.inflattices
open import order-theory.order-preserving-maps-posets
open import order-theory.posets
open import order-theory.suplattices
```

</details>

## Idea

{{#concept "Kleene's fixed point theorem" WD="Kleene fixed-point theorem" WDID=Q3527263}}
states that every
[Scott-continuous](domain-theory.scott-continuous-maps-posets.md) endomap
`f : 𝒜 → 𝒜` on an inhabited
[directed complete poset](domain-theory.directed-complete-posets.md) `𝒜` has a
[fixed point](foundation.fixed-points-endofunctions.md), and if `𝒜` has a bottom
element, then `f` has a least fixed point.

## Theorem

### Kleene's fixed point theorem for suplattices

```agda
module _
  {l1 l2 : Level}
  (𝒜 : Directed-Complete-Poset l1 l2 lzero)
  (f : type-Directed-Complete-Poset 𝒜 → type-Directed-Complete-Poset 𝒜)
  (F :
    is-scott-continuous-map-Poset
      ( poset-Directed-Complete-Poset 𝒜)
      ( poset-Directed-Complete-Poset 𝒜)
      ( lzero)
      ( f))
  (x : type-Directed-Complete-Poset 𝒜)
  where

  indexing-type-kleene-Directed-Complete-Poset : UU lzero
  indexing-type-kleene-Directed-Complete-Poset = ℕ

  is-inhabited-indexing-type-kleene-Directed-Complete-Poset :
    is-inhabited indexing-type-kleene-Directed-Complete-Poset
  is-inhabited-indexing-type-kleene-Directed-Complete-Poset =
    unit-trunc-Prop zero-ℕ

  indexing-inhabited-type-kleene-Directed-Complete-Poset : Inhabited-Type lzero
  indexing-inhabited-type-kleene-Directed-Complete-Poset =
    indexing-type-kleene-Directed-Complete-Poset ,
    is-inhabited-indexing-type-kleene-Directed-Complete-Poset

  family-of-elements-kleene-Directed-Complete-Poset :
    indexing-type-kleene-Directed-Complete-Poset →
    type-Directed-Complete-Poset 𝒜
  family-of-elements-kleene-Directed-Complete-Poset n = iterate n f x

  is-directed-family-of-elements-kleene-Directed-Complete-Poset :
    is-directed-family-Poset
      ( poset-Directed-Complete-Poset 𝒜)
      ( indexing-inhabited-type-kleene-Directed-Complete-Poset)
      ( family-of-elements-kleene-Directed-Complete-Poset)
  is-directed-family-of-elements-kleene-Directed-Complete-Poset u v =
    {!   !}

  directed-family-of-elements-kleene-Directed-Complete-Poset :
    directed-family-Poset lzero (poset-Directed-Complete-Poset 𝒜)
  directed-family-of-elements-kleene-Directed-Complete-Poset =
    indexing-inhabited-type-kleene-Directed-Complete-Poset ,
    family-of-elements-kleene-Directed-Complete-Poset ,
    is-directed-family-of-elements-kleene-Directed-Complete-Poset

  point-kleene-Directed-Complete-Poset : type-Directed-Complete-Poset 𝒜
  point-kleene-Directed-Complete-Poset =
    sup-Directed-Complete-Poset 𝒜
      ( directed-family-of-elements-kleene-Directed-Complete-Poset)

  leq-point-kleene-Directed-Complete-Poset :
    leq-Directed-Complete-Poset 𝒜
      ( point-kleene-Directed-Complete-Poset)
      ( f point-kleene-Directed-Complete-Poset)
  leq-point-kleene-Directed-Complete-Poset = {!   !}

  geq-point-kleene-Directed-Complete-Poset :
    leq-Directed-Complete-Poset 𝒜
      ( f point-kleene-Directed-Complete-Poset)
      ( point-kleene-Directed-Complete-Poset)
  geq-point-kleene-Directed-Complete-Poset = {!   !}

  is-fixed-point-kleene-Directed-Complete-Poset :
    f ( point-kleene-Directed-Complete-Poset) ＝
    point-kleene-Directed-Complete-Poset
  is-fixed-point-kleene-Directed-Complete-Poset =
    antisymmetric-leq-Directed-Complete-Poset 𝒜
      ( f (point-kleene-Directed-Complete-Poset))
      ( point-kleene-Directed-Complete-Poset)
      ( geq-point-kleene-Directed-Complete-Poset)
      ( leq-point-kleene-Directed-Complete-Poset)

  fixed-point-kleene-Directed-Complete-Poset : fixed-point f
  fixed-point-kleene-Directed-Complete-Poset =
    point-kleene-Directed-Complete-Poset ,
    is-fixed-point-kleene-Directed-Complete-Poset
```

### Kleene's fixed point theorem for directed complete posets with a bottom element

> TODO

## External links

- [Kleene fixed-point theorem](https://en.wikipedia.org/wiki/Kleene_fixed-point_theorem)
  at Wikipedia
- [Kleene's fixed point theorem](https://ncatlab.org/nlab/show/Kleene%27s+fixed+point+theorem)
  at $n$Lab
