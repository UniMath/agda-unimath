# Kleene's fixed point theorem for directed complete posets

```agda
module domain-theory.kleenes-fixed-point-theorem-directed-complete-posets where
```

<details><summary>Imports</summary>

```agda
open import domain-theory.directed-complete-posets
open import domain-theory.directed-families-posets
open import domain-theory.scott-continuous-maps-posets

open import elementary-number-theory.decidable-total-order-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.conjunction
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.fixed-points-endofunctions
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

### Kleene's fixed point theorem for directed complete posets

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
  (p : leq-Directed-Complete-Poset 𝒜 x (f x))
  where

  leq-iterate-kleene-Directed-Complete-Poset :
    (n : ℕ) →
    leq-Directed-Complete-Poset 𝒜 (iterate n f x) (iterate (succ-ℕ n) f x)
  leq-iterate-kleene-Directed-Complete-Poset zero-ℕ = p
  leq-iterate-kleene-Directed-Complete-Poset (succ-ℕ n) =
    preserves-order-is-scott-continuous-map-Poset
      ( poset-Directed-Complete-Poset 𝒜)
      ( poset-Directed-Complete-Poset 𝒜)
      ( F)
      ( iterate n f x)
      ( iterate (succ-ℕ n) f x)
      ( leq-iterate-kleene-Directed-Complete-Poset n)

  hom-kleene-Directed-Complete-Poset :
    hom-Poset ℕ-Poset (poset-Directed-Complete-Poset 𝒜)
  hom-kleene-Directed-Complete-Poset =
    hom-ind-ℕ-Poset
      ( poset-Directed-Complete-Poset 𝒜)
      ( λ n → iterate n f x)
      ( leq-iterate-kleene-Directed-Complete-Poset)

  indexing-type-kleene-Directed-Complete-Poset : UU lzero
  indexing-type-kleene-Directed-Complete-Poset = ℕ

  is-inhabited-indexing-type-kleene-Directed-Complete-Poset :
    is-inhabited indexing-type-kleene-Directed-Complete-Poset
  is-inhabited-indexing-type-kleene-Directed-Complete-Poset =
    unit-trunc-Prop 0

  indexing-inhabited-type-kleene-Directed-Complete-Poset : Inhabited-Type lzero
  indexing-inhabited-type-kleene-Directed-Complete-Poset =
    indexing-type-kleene-Directed-Complete-Poset ,
    is-inhabited-indexing-type-kleene-Directed-Complete-Poset

  family-kleene-Directed-Complete-Poset :
    ℕ → type-Directed-Complete-Poset 𝒜
  family-kleene-Directed-Complete-Poset n = iterate n f x

  preserves-order-family-kleene-Directed-Complete-Poset :
    preserves-order-Poset
      ( ℕ-Poset)
      ( poset-Directed-Complete-Poset 𝒜)
      ( family-kleene-Directed-Complete-Poset)
  preserves-order-family-kleene-Directed-Complete-Poset =
    preserves-order-ind-ℕ-Poset
      ( poset-Directed-Complete-Poset 𝒜)
      ( family-kleene-Directed-Complete-Poset)
      ( leq-iterate-kleene-Directed-Complete-Poset)

  is-directed-family-kleene-Directed-Complete-Poset :
    is-directed-family-Poset
      ( poset-Directed-Complete-Poset 𝒜)
      ( indexing-inhabited-type-kleene-Directed-Complete-Poset)
      ( family-kleene-Directed-Complete-Poset)
  is-directed-family-kleene-Directed-Complete-Poset n m =
    rec-coproduct
      ( λ p →
        intro-exists m
          ( preserves-order-family-kleene-Directed-Complete-Poset n m p ,
            preserves-order-family-kleene-Directed-Complete-Poset m m
              ( refl-leq-ℕ m)))
      ( λ p →
        intro-exists n
          ( preserves-order-family-kleene-Directed-Complete-Poset n n
            ( refl-leq-ℕ n) ,
            preserves-order-family-kleene-Directed-Complete-Poset m n p))
      ( linear-leq-ℕ n m)

  directed-family-kleene-Directed-Complete-Poset :
    directed-family-Poset lzero (poset-Directed-Complete-Poset 𝒜)
  directed-family-kleene-Directed-Complete-Poset =
    indexing-inhabited-type-kleene-Directed-Complete-Poset ,
    family-kleene-Directed-Complete-Poset ,
    is-directed-family-kleene-Directed-Complete-Poset

  point-kleene-Directed-Complete-Poset : type-Directed-Complete-Poset 𝒜
  point-kleene-Directed-Complete-Poset =
    sup-Directed-Complete-Poset 𝒜 directed-family-kleene-Directed-Complete-Poset

  leq-point-kleene-Directed-Complete-Poset :
    leq-Directed-Complete-Poset 𝒜
      ( point-kleene-Directed-Complete-Poset)
      ( f point-kleene-Directed-Complete-Poset)
  leq-point-kleene-Directed-Complete-Poset = {! pr1 (F ? ? ?) ? !}

  geq-point-kleene-Directed-Complete-Poset :
    leq-Directed-Complete-Poset 𝒜
      ( f point-kleene-Directed-Complete-Poset)
      ( point-kleene-Directed-Complete-Poset)
  geq-point-kleene-Directed-Complete-Poset =
    pr1
      ( F ( directed-family-kleene-Directed-Complete-Poset)
          ( is-directed-complete-Directed-Complete-Poset 𝒜
              directed-family-kleene-Directed-Complete-Poset)
          ( point-kleene-Directed-Complete-Poset))
      {!   !}

  is-fixed-point-kleene-Directed-Complete-Poset :
    f ( point-kleene-Directed-Complete-Poset) ＝
    point-kleene-Directed-Complete-Poset
  is-fixed-point-kleene-Directed-Complete-Poset =
    eq-is-least-upper-bound-family-of-elements-Poset
      ( poset-Directed-Complete-Poset 𝒜)
      (λ where a → {!  !})
      ( is-least-upper-bound-sup-Directed-Complete-Poset 𝒜
        ( directed-family-kleene-Directed-Complete-Poset))

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
