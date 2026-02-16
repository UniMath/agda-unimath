# Joins of finite families in large join semilattices

```agda
module order-theory.joins-finite-families-large-join-semilattices where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.univalence
open import foundation.universe-levels

open import group-theory.large-commutative-monoids
open import group-theory.sums-of-finite-families-of-elements-commutative-monoids
open import group-theory.sums-of-finite-sequences-of-elements-commutative-monoids

open import lists.finite-sequences

open import order-theory.joins-finite-families-join-semilattices
open import order-theory.large-join-semilattices
open import order-theory.least-upper-bounds-large-posets
open import order-theory.upper-bounds-large-posets

open import univalent-combinatorics.counting
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

In a [large join semilattice](order-theory.large-join-semilattices.md), every
family of elements indexed by a
[finite type](univalent-combinatorics.finite-types.md) has a
[least upper bound](order-theory.least-upper-bounds-large-posets.md).

## Definition

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (L : Large-Join-Semilattice α β)
  where

  join-fin-sequence-type-Large-Join-Semilattice :
    {l : Level} (n : ℕ) → fin-sequence (type-Large-Join-Semilattice L l) n →
    type-Large-Join-Semilattice L l
  join-fin-sequence-type-Large-Join-Semilattice {l} =
    sum-fin-sequence-type-Commutative-Monoid
      ( commutative-monoid-Large-Join-Semilattice L l)

  join-counted-family-type-Large-Join-Semilattice :
    {l1 l2 : Level} (I : UU l1) → count I →
    (I → type-Large-Join-Semilattice L l2) → type-Large-Join-Semilattice L l2
  join-counted-family-type-Large-Join-Semilattice {l1} {l2} =
    sum-count-Commutative-Monoid
      ( commutative-monoid-Large-Join-Semilattice L l2)

  join-finite-family-type-Large-Join-Semilattice :
    {l1 l2 : Level} (I : Finite-Type l1) →
    (type-Finite-Type I → type-Large-Join-Semilattice L l2) →
    type-Large-Join-Semilattice L l2
  join-finite-family-type-Large-Join-Semilattice {l1} {l2} =
    sum-finite-Commutative-Monoid
      ( commutative-monoid-Large-Join-Semilattice L l2)
```

## Properties

### The join of a finite sequence of elements is its least upper bound

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (L : Large-Join-Semilattice α β)
  where

  abstract
    is-least-upper-bound-join-fin-sequence-type-Large-Join-Semilattice :
      {l : Level} (n : ℕ) →
      (u : fin-sequence (type-Large-Join-Semilattice L l) n) →
      is-least-upper-bound-family-of-elements-Large-Poset
        ( large-poset-Large-Join-Semilattice L)
        ( u)
        ( join-fin-sequence-type-Large-Join-Semilattice L n u)
    pr1
      ( is-least-upper-bound-join-fin-sequence-type-Large-Join-Semilattice
        0 u z)
      _ =
      inv-tr
        ( λ x → leq-Large-Join-Semilattice L x z)
        ( raise-bottom-Large-Join-Semilattice L)
        ( is-bottom-element-bottom-Large-Join-Semilattice L _ z)
    pr2
      ( is-least-upper-bound-join-fin-sequence-type-Large-Join-Semilattice
        0 u z)
      _ ()
    pr1
      ( is-least-upper-bound-join-fin-sequence-type-Large-Join-Semilattice
        (succ-ℕ n) u z)
      Πi:uᵢ≤z =
      leq-join-Large-Join-Semilattice L _ _ _
        ( forward-implication
          ( is-least-upper-bound-join-fin-sequence-type-Large-Join-Semilattice
            ( n)
            ( u ∘ inl-Fin n)
            ( z))
          ( Πi:uᵢ≤z ∘ inl-Fin n))
        ( Πi:uᵢ≤z (neg-one-Fin n))
    pr2
      ( is-least-upper-bound-join-fin-sequence-type-Large-Join-Semilattice
        (succ-ℕ n) u z)
      v≤z (inr _) =
      transitive-leq-Large-Join-Semilattice L _ _ _
        ( v≤z)
        ( leq-right-join-Large-Join-Semilattice L _ _)
    pr2
      ( is-least-upper-bound-join-fin-sequence-type-Large-Join-Semilattice
        (succ-ℕ n) u z)
      v≤z (inl i) =
      backward-implication
        ( is-least-upper-bound-join-fin-sequence-type-Large-Join-Semilattice
          ( n)
          ( u ∘ inl-Fin n)
          ( z))
        ( transitive-leq-Large-Join-Semilattice L _ _ _
          ( v≤z)
          ( leq-left-join-Large-Join-Semilattice L _ _))
        ( i)
```

### The join of a counted family is its least upper bound

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (L : Large-Join-Semilattice α β)
  {l1 l2 : Level}
  (I : UU l1)
  (cI@(nI , Fin-n≃I) : count I)
  (f : I → type-Large-Join-Semilattice L l2)
  where

  abstract
    is-least-upper-bound-join-counted-family-type-Large-Join-Semilattice :
      is-least-upper-bound-family-of-elements-Large-Poset
        ( large-poset-Large-Join-Semilattice L)
        ( f)
        ( join-counted-family-type-Large-Join-Semilattice L I cI f)
    is-least-upper-bound-join-counted-family-type-Large-Join-Semilattice z =
      ( is-least-upper-bound-join-fin-sequence-type-Large-Join-Semilattice L
        ( nI)
        ( f ∘ map-equiv Fin-n≃I)
        ( z)) ∘iff
      ( iff-equiv
        ( equiv-Π
          ( _)
          ( inv-equiv Fin-n≃I)
          ( λ i →
            equiv-inv-tr
              ( λ j → leq-Large-Join-Semilattice L (f j) z)
              ( is-section-map-inv-equiv Fin-n≃I i))))
```

### The join of a finite family is equal to the join of any count for it

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (L : Large-Join-Semilattice α β)
  {l1 l2 : Level}
  (I : Finite-Type l1)
  (cI : count (type-Finite-Type I))
  (f : type-Finite-Type I → type-Large-Join-Semilattice L l2)
  where

  abstract
    eq-join-finite-family-join-counted-family-type-Large-Join-Semilattice :
      join-finite-family-type-Large-Join-Semilattice L I f ＝
      join-counted-family-type-Large-Join-Semilattice L _ cI f
    eq-join-finite-family-join-counted-family-type-Large-Join-Semilattice =
      eq-sum-finite-sum-count-Commutative-Monoid
        ( commutative-monoid-Large-Join-Semilattice L l2)
        ( I)
        ( cI)
        ( f)
```

### The join of a finite family is its least upper bound

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (L : Large-Join-Semilattice α β)
  (let P = large-poset-Large-Join-Semilattice L)
  {l1 l2 : Level}
  (I@(type-I , is-finite-I) : Finite-Type l1)
  (f : type-I → type-Large-Join-Semilattice L l2)
  where

  abstract
    is-least-upper-bound-join-finite-family-type-Large-Join-Semilattice :
      is-least-upper-bound-family-of-elements-Large-Poset
        ( P)
        ( f)
        ( join-finite-family-type-Large-Join-Semilattice L I f)
    is-least-upper-bound-join-finite-family-type-Large-Join-Semilattice z =
      let
        motive x =
          iff-Prop
            ( is-upper-bound-prop-family-of-elements-Large-Poset P f z)
            ( leq-prop-Large-Join-Semilattice L x z)
      in
        rec-trunc-Prop
          ( motive (join-finite-family-type-Large-Join-Semilattice L I f))
          ( λ cI →
            inv-tr
              ( is-in-subtype motive)
              ( eq-join-finite-family-join-counted-family-type-Large-Join-Semilattice
                ( L)
                ( I)
                ( cI)
                ( f))
              ( is-least-upper-bound-join-counted-family-type-Large-Join-Semilattice
                ( L)
                ( type-I)
                ( cI)
                ( f)
                ( z)))
          ( is-finite-I)
```
