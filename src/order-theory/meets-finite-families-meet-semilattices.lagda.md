# Meets of finite families of elements in meet-semilattices

```agda
module order-theory.meets-finite-families-meet-semilattices where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.univalence
open import foundation.universe-levels

open import group-theory.commutative-semigroups
open import group-theory.sums-of-finite-families-of-elements-commutative-semigroups
open import group-theory.sums-of-finite-sequences-of-elements-commutative-semigroups

open import lists.finite-sequences

open import order-theory.greatest-lower-bounds-posets
open import order-theory.meet-semilattices

open import univalent-combinatorics.counting
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.inhabited-finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

In a [meet semilattice](order-theory.meet-semilattices.md), the meet of any
family of elements indexed by an
[inhabited finite type](univalent-combinatorics.inhabited-finite-types.md) is
their [greatest lower bound](order-theory.greatest-lower-bounds-posets.md).

## Definition

### The meet of a finite sequence of elements

```agda
module _
  {l1 l2 : Level} (X : Order-Theoretic-Meet-Semilattice l1 l2)
  where

  meet-fin-sequence-type-Order-Theoretic-Meet-Semilattice :
    (n : ℕ) →
    fin-sequence (type-Order-Theoretic-Meet-Semilattice X) (succ-ℕ n) →
    type-Order-Theoretic-Meet-Semilattice X
  meet-fin-sequence-type-Order-Theoretic-Meet-Semilattice =
    sum-fin-sequence-type-Commutative-Semigroup
      ( commutative-semigroup-Order-Theoretic-Meet-Semilattice X)
```

### The meet of a family of elements indexed by an inhabited counted type

```agda
module _
  {l1 l2 : Level} (X : Order-Theoretic-Meet-Semilattice l1 l2)
  {l3 : Level} (I : UU l3) (|I| : is-inhabited I) (cI : count I)
  where

  meet-counted-family-type-Order-Theoretic-Meet-Semilattice :
    (f : I → type-Order-Theoretic-Meet-Semilattice X) →
    type-Order-Theoretic-Meet-Semilattice X
  meet-counted-family-type-Order-Theoretic-Meet-Semilattice =
    sum-count-Commutative-Semigroup
      ( commutative-semigroup-Order-Theoretic-Meet-Semilattice X)
      ( I)
      ( |I|)
      ( cI)
```

### The meet of a family of elements indexed by an inhabited finite type

```agda
module _
  {l1 l2 : Level} (X : Order-Theoretic-Meet-Semilattice l1 l2)
  {l3 : Level} (I : Inhabited-Finite-Type l3)
  where

  meet-inhabited-finite-family-Order-Theoretic-Meet-Semilattice :
    (f :
      type-Inhabited-Finite-Type I → type-Order-Theoretic-Meet-Semilattice X) →
    type-Order-Theoretic-Meet-Semilattice X
  meet-inhabited-finite-family-Order-Theoretic-Meet-Semilattice =
    sum-finite-Commutative-Semigroup
      ( commutative-semigroup-Order-Theoretic-Meet-Semilattice X)
      ( I)
```

## Properties

### The meet of a nonempty finite sequence is its least upper bound

```agda
module _
  {l1 l2 : Level} (X : Order-Theoretic-Meet-Semilattice l1 l2)
  where

  abstract
    is-greatest-lower-bound-meet-fin-sequence-type-Order-Theoretic-Meet-Semilattice :
      (n : ℕ) →
      (x : fin-sequence (type-Order-Theoretic-Meet-Semilattice X) (succ-ℕ n)) →
      is-greatest-lower-bound-family-of-elements-Poset
        ( poset-Order-Theoretic-Meet-Semilattice X)
        ( x)
        ( meet-fin-sequence-type-Order-Theoretic-Meet-Semilattice X n x)
    pr1
      ( is-greatest-lower-bound-meet-fin-sequence-type-Order-Theoretic-Meet-Semilattice
        zero-ℕ x y) y≤xᵢ = y≤xᵢ (neg-one-Fin zero-ℕ)
    pr2
      ( is-greatest-lower-bound-meet-fin-sequence-type-Order-Theoretic-Meet-Semilattice
        zero-ℕ x y) y≤min (inr star) = y≤min
    pr1
      ( is-greatest-lower-bound-meet-fin-sequence-type-Order-Theoretic-Meet-Semilattice
        (succ-ℕ n) x y) y≤xᵢ =
          leq-meet-Order-Theoretic-Meet-Semilattice X
            ( forward-implication
              ( is-greatest-lower-bound-meet-fin-sequence-type-Order-Theoretic-Meet-Semilattice
                ( n)
                ( x ∘ inl)
                ( y))
              ( y≤xᵢ ∘ inl))
            ( y≤xᵢ (inr star))
    pr2
      ( is-greatest-lower-bound-meet-fin-sequence-type-Order-Theoretic-Meet-Semilattice
        (succ-ℕ n) x y) y≤meet (inr star) =
          transitive-leq-Order-Theoretic-Meet-Semilattice X y _ (x (inr star))
            ( leq-right-meet-Order-Theoretic-Meet-Semilattice X _ _)
            ( y≤meet)
    pr2
      ( is-greatest-lower-bound-meet-fin-sequence-type-Order-Theoretic-Meet-Semilattice
        (succ-ℕ n) x y) y≤meet (inl i) =
          backward-implication
            ( is-greatest-lower-bound-meet-fin-sequence-type-Order-Theoretic-Meet-Semilattice
              ( n)
              ( x ∘ inl)
              ( y))
            ( transitive-leq-Order-Theoretic-Meet-Semilattice X y _ _
              ( leq-left-meet-Order-Theoretic-Meet-Semilattice X _ _)
              ( y≤meet))
            ( i)
```

### The meet of a counted family of elements is its least upper bound

```agda
abstract
  is-greatest-lower-bound-meet-counted-family-type-Order-Theoretic-Meet-Semilattice :
    {l1 l2 : Level} (X : Order-Theoretic-Meet-Semilattice l1 l2) →
    {l3 : Level} (I : UU l3) (|I| : is-inhabited I) (cI : count I) →
    (f : I → type-Order-Theoretic-Meet-Semilattice X) →
    is-greatest-lower-bound-family-of-elements-Poset
      ( poset-Order-Theoretic-Meet-Semilattice X)
      ( f)
      ( meet-counted-family-type-Order-Theoretic-Meet-Semilattice X I |I| cI f)
  is-greatest-lower-bound-meet-counted-family-type-Order-Theoretic-Meet-Semilattice
    X I |I| cI@(zero-ℕ , _) _ =
      ex-falso
        ( is-nonempty-is-inhabited
          ( |I|)
          ( is-empty-is-zero-number-of-elements-count cI refl))
  is-greatest-lower-bound-meet-counted-family-type-Order-Theoretic-Meet-Semilattice
    X I |I| cI@(succ-ℕ n , Fin-sn≃I) f y =
      is-greatest-lower-bound-meet-fin-sequence-type-Order-Theoretic-Meet-Semilattice
        ( X)
        ( n)
        ( f ∘ map-equiv Fin-sn≃I)
        ( y) ∘iff
      iff-equiv
        ( equiv-Π _
          ( inv-equiv Fin-sn≃I)
          ( λ i →
            equiv-eq
              ( ap
                ( λ j → leq-Order-Theoretic-Meet-Semilattice X y (f j))
                ( inv (is-section-map-inv-equiv Fin-sn≃I i)))))
```

### The meet of an inhabited finite family of elements is its least upper bound

```agda
module _
  {l1 l2 l3 : Level} (X : Order-Theoretic-Meet-Semilattice l1 l2)
  (I : Inhabited-Finite-Type l3)
  where

  abstract
    is-greatest-lower-bound-meet-inhabited-finite-family-Order-Theoretic-Meet-Semilattice :
      (f :
        type-Inhabited-Finite-Type I →
        type-Order-Theoretic-Meet-Semilattice X) →
      is-greatest-lower-bound-family-of-elements-Poset
        ( poset-Order-Theoretic-Meet-Semilattice X)
        ( f)
        ( meet-inhabited-finite-family-Order-Theoretic-Meet-Semilattice X I f)
    is-greatest-lower-bound-meet-inhabited-finite-family-Order-Theoretic-Meet-Semilattice
      f =
        rec-trunc-Prop
          ( is-greatest-lower-bound-family-of-elements-prop-Poset
            ( poset-Order-Theoretic-Meet-Semilattice X)
            ( f)
            ( _))
          ( λ cI →
            inv-tr
              ( is-greatest-lower-bound-family-of-elements-Poset
                ( poset-Order-Theoretic-Meet-Semilattice X)
                ( f))
              ( eq-sum-finite-sum-count-Commutative-Semigroup
                ( commutative-semigroup-Order-Theoretic-Meet-Semilattice X)
                ( I)
                ( cI)
                ( f))
              ( is-greatest-lower-bound-meet-counted-family-type-Order-Theoretic-Meet-Semilattice
                ( X)
                ( type-Inhabited-Finite-Type I)
                ( is-inhabited-type-Inhabited-Finite-Type I)
                ( cI)
                ( f)))
          ( is-finite-Inhabited-Finite-Type I)
```
