# Joins of finite families of elements in join-semilattices

```agda
module order-theory.joins-finite-families-join-semilattices where
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
open import group-theory.products-of-finite-families-of-elements-commutative-semigroups
open import group-theory.products-of-finite-sequences-of-elements-commutative-semigroups

open import lists.finite-sequences

open import order-theory.join-semilattices
open import order-theory.least-upper-bounds-posets

open import univalent-combinatorics.counting
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.inhabited-finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

In a [join-semilattice](order-theory.join-semilattices.md), the join of any
family of elements indexed by an
[inhabited finite type](univalent-combinatorics.inhabited-finite-types.md) is
their [least upper bound](order-theory.least-upper-bounds-posets.md).

## Definition

### The join of a finite sequence of elements

```agda
module _
  {l1 l2 : Level} (X : Order-Theoretic-Join-Semilattice l1 l2)
  where

  join-fin-sequence-type-Order-Theoretic-Join-Semilattice :
    (n : ℕ) →
    fin-sequence (type-Order-Theoretic-Join-Semilattice X) (succ-ℕ n) →
    type-Order-Theoretic-Join-Semilattice X
  join-fin-sequence-type-Order-Theoretic-Join-Semilattice =
    product-fin-sequence-type-Commutative-Semigroup
      ( commutative-semigroup-Order-Theoretic-Join-Semilattice X)
```

### The join of a family of elements indexed by an inhabited counted type

```agda
module _
  {l1 l2 : Level} (X : Order-Theoretic-Join-Semilattice l1 l2)
  {l3 : Level} {I : UU l3} (|I| : is-inhabited I) (cI : count I)
  where

  join-counted-family-type-Order-Theoretic-Join-Semilattice :
    (f : I → type-Order-Theoretic-Join-Semilattice X) →
    type-Order-Theoretic-Join-Semilattice X
  join-counted-family-type-Order-Theoretic-Join-Semilattice =
    product-count-Commutative-Semigroup
      ( commutative-semigroup-Order-Theoretic-Join-Semilattice X)
      ( I)
      ( |I|)
      ( cI)
```

### The join of a family of elements indexed by an inhabited finite type

```agda
module _
  {l1 l2 : Level} (X : Order-Theoretic-Join-Semilattice l1 l2)
  {l3 : Level} (I : Inhabited-Finite-Type l3)
  where

  join-inhabited-finite-family-Order-Theoretic-Join-Semilattice :
    (f :
      type-Inhabited-Finite-Type I → type-Order-Theoretic-Join-Semilattice X) →
    type-Order-Theoretic-Join-Semilattice X
  join-inhabited-finite-family-Order-Theoretic-Join-Semilattice =
    product-finite-Commutative-Semigroup
      ( commutative-semigroup-Order-Theoretic-Join-Semilattice X)
      ( I)
```

## Properties

### The join of a nonempty finite sequence is its least upper bound

```agda
module _
  {l1 l2 : Level} (X : Order-Theoretic-Join-Semilattice l1 l2)
  where

  abstract
    is-least-upper-bound-join-fin-sequence-type-Order-Theoretic-Join-Semilattice :
      (n : ℕ) →
      (x : fin-sequence (type-Order-Theoretic-Join-Semilattice X) (succ-ℕ n)) →
      is-least-upper-bound-family-of-elements-Poset
        ( poset-Order-Theoretic-Join-Semilattice X)
        ( x)
        ( join-fin-sequence-type-Order-Theoretic-Join-Semilattice X n x)
    pr1
      ( is-least-upper-bound-join-fin-sequence-type-Order-Theoretic-Join-Semilattice
        zero-ℕ x y) y≤xᵢ =
        y≤xᵢ (neg-one-Fin 0)
    pr2
      ( is-least-upper-bound-join-fin-sequence-type-Order-Theoretic-Join-Semilattice
        zero-ℕ x y) y≤x₀ (inr star) = y≤x₀
    pr1
      ( is-least-upper-bound-join-fin-sequence-type-Order-Theoretic-Join-Semilattice
        (succ-ℕ n) x y) y≤xᵢ =
          leq-join-Order-Theoretic-Join-Semilattice X
            ( forward-implication
              ( is-least-upper-bound-join-fin-sequence-type-Order-Theoretic-Join-Semilattice
                ( n)
                ( x ∘ inl)
                ( y))
              ( y≤xᵢ ∘ inl))
            ( y≤xᵢ (neg-one-Fin (succ-ℕ n)))
    pr2
      ( is-least-upper-bound-join-fin-sequence-type-Order-Theoretic-Join-Semilattice
        (succ-ℕ n) x y) max-x≤y (inr star) =
          transitive-leq-Order-Theoretic-Join-Semilattice X (x (inr star)) _ y
            ( max-x≤y)
            ( leq-right-join-Order-Theoretic-Join-Semilattice X _ _)
    pr2
      ( is-least-upper-bound-join-fin-sequence-type-Order-Theoretic-Join-Semilattice
        (succ-ℕ n) x y) max-x≤y (inl i) =
          backward-implication
            ( is-least-upper-bound-join-fin-sequence-type-Order-Theoretic-Join-Semilattice
              ( n)
              ( x ∘ inl)
              ( y))
            ( transitive-leq-Order-Theoretic-Join-Semilattice X _ _ y
              ( max-x≤y)
              ( leq-left-join-Order-Theoretic-Join-Semilattice X _ _))
            ( i)

  has-least-upper-bound-join-fin-sequence-type-Order-Theoretic-Join-Semilattice :
    (n : ℕ) →
    (x : fin-sequence (type-Order-Theoretic-Join-Semilattice X) (succ-ℕ n)) →
    has-least-upper-bound-family-of-elements-Poset
      ( poset-Order-Theoretic-Join-Semilattice X)
      ( x)
  has-least-upper-bound-join-fin-sequence-type-Order-Theoretic-Join-Semilattice
    n x =
      ( join-fin-sequence-type-Order-Theoretic-Join-Semilattice X n x ,
        is-least-upper-bound-join-fin-sequence-type-Order-Theoretic-Join-Semilattice
          ( n)
          ( x))
```

### The join of a counted family of elements is its least upper bound

```agda
abstract
  is-least-upper-bound-join-counted-family-type-Order-Theoretic-Join-Semilattice :
    {l1 l2 : Level} (X : Order-Theoretic-Join-Semilattice l1 l2) →
    {l3 : Level} {I : UU l3} (|I| : is-inhabited I) (cI : count I) →
    (f : I → type-Order-Theoretic-Join-Semilattice X) →
    is-least-upper-bound-family-of-elements-Poset
      ( poset-Order-Theoretic-Join-Semilattice X)
      ( f)
      ( join-counted-family-type-Order-Theoretic-Join-Semilattice X |I| cI f)
  is-least-upper-bound-join-counted-family-type-Order-Theoretic-Join-Semilattice
    X |I| cI@(zero-ℕ , _) _ =
      ex-falso
        ( is-nonempty-is-inhabited
          ( |I|)
          ( is-empty-is-zero-number-of-elements-count cI refl))
  is-least-upper-bound-join-counted-family-type-Order-Theoretic-Join-Semilattice
    X |I| cI@(succ-ℕ n , Fin-sn≃I) f y =
      is-least-upper-bound-join-fin-sequence-type-Order-Theoretic-Join-Semilattice
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
                ( λ j → leq-Order-Theoretic-Join-Semilattice X (f j) y)
                ( inv (is-section-map-inv-equiv Fin-sn≃I i)))))
```

### The join of an inhabited finite family of elements is its join over any count for that family

```agda
module _
  {l1 l2 l3 : Level} (X : Order-Theoretic-Join-Semilattice l1 l2)
  (I : Inhabited-Finite-Type l3) (cI : count (type-Inhabited-Finite-Type I))
  (f : type-Inhabited-Finite-Type I → type-Order-Theoretic-Join-Semilattice X)
  where

  abstract
    eq-join-inhabited-finite-family-join-counted-family-Order-Theoretic-Join-Semilattice :
      join-inhabited-finite-family-Order-Theoretic-Join-Semilattice X I f ＝
      join-counted-family-type-Order-Theoretic-Join-Semilattice
        ( X)
        ( is-inhabited-type-Inhabited-Finite-Type I)
        ( cI)
        ( f)
    eq-join-inhabited-finite-family-join-counted-family-Order-Theoretic-Join-Semilattice =
      eq-product-finite-product-count-Commutative-Semigroup
        ( commutative-semigroup-Order-Theoretic-Join-Semilattice X)
        ( I)
        ( cI)
        ( f)
```

### The join of an inhabited finite family of elements is its least upper bound

```agda
module _
  {l1 l2 l3 : Level} (X : Order-Theoretic-Join-Semilattice l1 l2)
  (I : Inhabited-Finite-Type l3)
  where

  abstract
    is-least-upper-bound-join-inhabited-finite-family-Order-Theoretic-Join-Semilattice :
      (f :
        type-Inhabited-Finite-Type I →
        type-Order-Theoretic-Join-Semilattice X) →
      is-least-upper-bound-family-of-elements-Poset
        ( poset-Order-Theoretic-Join-Semilattice X)
        ( f)
        ( join-inhabited-finite-family-Order-Theoretic-Join-Semilattice X I f)
    is-least-upper-bound-join-inhabited-finite-family-Order-Theoretic-Join-Semilattice
      f =
        rec-trunc-Prop
          ( is-least-upper-bound-family-of-elements-prop-Poset
            ( poset-Order-Theoretic-Join-Semilattice X)
            ( f)
            ( _))
          ( λ cI →
            inv-tr
              ( is-least-upper-bound-family-of-elements-Poset
                ( poset-Order-Theoretic-Join-Semilattice X)
                ( f))
              ( eq-join-inhabited-finite-family-join-counted-family-Order-Theoretic-Join-Semilattice
                ( X)
                ( I)
                ( cI)
                ( f))
              ( is-least-upper-bound-join-counted-family-type-Order-Theoretic-Join-Semilattice
                ( X)
                ( is-inhabited-type-Inhabited-Finite-Type I)
                ( cI)
                ( f)))
          ( is-finite-Inhabited-Finite-Type I)
```
