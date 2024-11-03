# Kleene's fixed point theorem for ω-complete posets

```agda
module domain-theory.kleenes-fixed-point-theorem-omega-complete-posets where
```

<details><summary>Imports</summary>

```agda
open import domain-theory.directed-families-posets
open import domain-theory.omega-complete-posets
open import domain-theory.omega-continuous-maps-posets

open import elementary-number-theory.decidable-total-order-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
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
open import order-theory.chains-posets
open import order-theory.inflattices
open import order-theory.inhabited-chains-posets
open import order-theory.order-preserving-maps-posets
open import order-theory.posets
open import order-theory.suplattices
```

</details>

## Idea

{{#concept "Kleene's fixed point theorem" Disambiguation="ω-complete posets" WD="Kleene fixed-point theorem" WDID=Q3527263}}
states that every [Scott-continuous](domain-theory.ω-continuous-maps-posets.md)
endomap `f : 𝒜 → 𝒜` on an inhabited
[ω-complete poset](domain-theory.omega-complete-posets.md) `𝒜` has a
[fixed point](foundation.fixed-points-endofunctions.md), and if `𝒜` has a bottom
element, then `f` has a least fixed point.

## Theorem

### Kleene's fixed point theorem for ω-complete posets

```agda
module _
  {l1 l2 : Level}
  (𝒜 : ω-Complete-Poset l1 l2)
  (f : type-ω-Complete-Poset 𝒜 → type-ω-Complete-Poset 𝒜)
  (F :
    is-ω-continuous-map-Poset
      ( poset-ω-Complete-Poset 𝒜)
      ( poset-ω-Complete-Poset 𝒜)
      ( f))
  (x : type-ω-Complete-Poset 𝒜)
  (p : leq-ω-Complete-Poset 𝒜 x (f x))
  where

  leq-iterate-kleene-ω-Complete-Poset :
    (n : ℕ) →
    leq-ω-Complete-Poset 𝒜 (iterate n f x) (iterate (succ-ℕ n) f x)
  leq-iterate-kleene-ω-Complete-Poset zero-ℕ = p
  leq-iterate-kleene-ω-Complete-Poset (succ-ℕ n) =
    preserves-order-is-ω-continuous-map-Poset
      ( poset-ω-Complete-Poset 𝒜)
      ( poset-ω-Complete-Poset 𝒜)
      ( F)
      ( iterate n f x)
      ( iterate (succ-ℕ n) f x)
      ( leq-iterate-kleene-ω-Complete-Poset n)

  hom-kleene-ω-Complete-Poset :
    hom-Poset ℕ-Poset (poset-ω-Complete-Poset 𝒜)
  hom-kleene-ω-Complete-Poset =
    hom-ind-ℕ-Poset
      ( poset-ω-Complete-Poset 𝒜)
      ( λ n → iterate n f x)
      ( leq-iterate-kleene-ω-Complete-Poset)

  chain-kleene-ω-Complete-Poset :
    chain-Poset l1 (poset-ω-Complete-Poset 𝒜)
  chain-kleene-ω-Complete-Poset =
    chain-hom-total-order-Poset
      ( poset-ω-Complete-Poset 𝒜)
      ( ℕ-Total-Order)
      ( hom-kleene-ω-Complete-Poset)

  is-inhabited-chain-kleene-ω-Complete-Poset :
    is-inhabited-chain-Poset
      ( poset-ω-Complete-Poset 𝒜)
      ( chain-kleene-ω-Complete-Poset)
  is-inhabited-chain-kleene-ω-Complete-Poset =
    unit-trunc-Prop (x , unit-trunc-Prop (0 , refl))

  inhabited-chain-kleene-ω-Complete-Poset :
    inhabited-chain-Poset l1 (poset-ω-Complete-Poset 𝒜)
  inhabited-chain-kleene-ω-Complete-Poset =
    chain-kleene-ω-Complete-Poset ,
    is-inhabited-chain-kleene-ω-Complete-Poset

  indexing-type-kleene-ω-Complete-Poset : UU lzero
  indexing-type-kleene-ω-Complete-Poset = ℕ

  is-inhabited-indexing-type-kleene-ω-Complete-Poset :
    is-inhabited indexing-type-kleene-ω-Complete-Poset
  is-inhabited-indexing-type-kleene-ω-Complete-Poset =
    unit-trunc-Prop 0

  indexing-inhabited-type-kleene-ω-Complete-Poset : Inhabited-Type lzero
  indexing-inhabited-type-kleene-ω-Complete-Poset =
    indexing-type-kleene-ω-Complete-Poset ,
    is-inhabited-indexing-type-kleene-ω-Complete-Poset

  directed-family-kleene-ω-Complete-Poset :
    directed-family-Poset l1 (poset-ω-Complete-Poset 𝒜)
  directed-family-kleene-ω-Complete-Poset =
    directed-family-inhabited-chain-Poset
      ( poset-ω-Complete-Poset 𝒜)
      ( inhabited-chain-kleene-ω-Complete-Poset)

  point-kleene-ω-Complete-Poset : type-ω-Complete-Poset 𝒜
  point-kleene-ω-Complete-Poset = {!  sup-ω-Complete-Poset 𝒜 ? !}
    -- sup-ω-Complete-Poset 𝒜
    --   ( directed-family-kleene-ω-Complete-Poset)

  -- leq-point-kleene-ω-Complete-Poset :
  --   leq-ω-Complete-Poset 𝒜
  --     ( point-kleene-ω-Complete-Poset)
  --     ( f point-kleene-ω-Complete-Poset)
  -- leq-point-kleene-ω-Complete-Poset = {!   !}

  -- geq-point-kleene-ω-Complete-Poset :
  --   leq-ω-Complete-Poset 𝒜
  --     ( f point-kleene-ω-Complete-Poset)
  --     ( point-kleene-ω-Complete-Poset)
  -- geq-point-kleene-ω-Complete-Poset = {!   !}

  -- is-fixed-point-kleene-ω-Complete-Poset :
  --   f ( point-kleene-ω-Complete-Poset) ＝
  --   point-kleene-ω-Complete-Poset
  -- is-fixed-point-kleene-ω-Complete-Poset =
  --   antisymmetric-leq-ω-Complete-Poset 𝒜
  --     ( f (point-kleene-ω-Complete-Poset))
  --     ( point-kleene-ω-Complete-Poset)
  --     ( geq-point-kleene-ω-Complete-Poset)
  --     ( leq-point-kleene-ω-Complete-Poset)

  -- fixed-point-kleene-ω-Complete-Poset : fixed-point f
  -- fixed-point-kleene-ω-Complete-Poset =
  --   point-kleene-ω-Complete-Poset ,
  --   is-fixed-point-kleene-ω-Complete-Poset
```

### Kleene's fixed point theorem for ω-complete posets with a bottom element

> TODO

## External links

- [Kleene fixed-point theorem](https://en.wikipedia.org/wiki/Kleene_fixed-point_theorem)
  at Wikipedia
- [Kleene's fixed point theorem](https://ncatlab.org/nlab/show/Kleene%27s+fixed+point+theorem)
  at $n$Lab
