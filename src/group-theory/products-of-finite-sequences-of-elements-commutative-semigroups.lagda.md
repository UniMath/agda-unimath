# Products of finite sequences of elements in commutative semigroups

```agda
{-# OPTIONS --lossy-unification #-}

module group-theory.products-of-finite-sequences-of-elements-commutative-semigroups where
```

<details><productmary>Imports</productmary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import finite-group-theory.permutations-standard-finite-types
open import finite-group-theory.transpositions-standard-finite-types

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.negated-equality
open import foundation.propositions
open import foundation.unit-type
open import foundation.universe-levels

open import group-theory.commutative-semigroups
open import group-theory.products-of-finite-sequences-of-elements-semigroups

open import linear-algebra.finite-sequences-in-commutative-semigroups

open import lists.lists

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The
{{#concept "product operation" Disambiguation="of a finite sequence in a commutative semigroup" Agda=product-fin-sequence-type-Commutative-Semigroup}}
extends the binary operation on a
[commutative semigroup](group-theory.commutative-semigroups.md) `G` to any
nonempty [finite sequence](lists.finite-sequences.md) of elements of `G`.

## Definition

```agda
product-fin-sequence-type-Commutative-Semigroup :
  {l : Level} (G : Commutative-Semigroup l) (n : ℕ) →
  fin-sequence-type-Commutative-Semigroup G (succ-ℕ n) →
  type-Commutative-Semigroup G
product-fin-sequence-type-Commutative-Semigroup G =
  product-fin-sequence-type-Semigroup (semigroup-Commutative-Semigroup G)
```

## Properties

### Products are homotopy invariant

```agda
module _
  {l : Level} (G : Commutative-Semigroup l)
  where

  abstract
    htpy-product-fin-sequence-type-Commutative-Semigroup :
      (n : ℕ) {f g : fin-sequence-type-Commutative-Semigroup G (succ-ℕ n)} →
      (f ~ g) →
      product-fin-sequence-type-Commutative-Semigroup G n f ＝
      product-fin-sequence-type-Commutative-Semigroup G n g
    htpy-product-fin-sequence-type-Commutative-Semigroup =
      htpy-product-fin-sequence-type-Semigroup
        ( semigroup-Commutative-Semigroup G)
```

### Splitting products of `succ-ℕ n + succ-ℕ m` elements into a product of `succ-ℕ n` elements and a product of `succ-ℕ m` elements

```agda
abstract
  split-product-fin-sequence-type-Commutative-Semigroup :
    {l : Level} (G : Commutative-Semigroup l)
    (n m : ℕ) →
    (f : fin-sequence-type-Commutative-Semigroup G (succ-ℕ n +ℕ succ-ℕ m)) →
    product-fin-sequence-type-Commutative-Semigroup G (succ-ℕ n +ℕ m) f ＝
    mul-Commutative-Semigroup G
      ( product-fin-sequence-type-Commutative-Semigroup G n
        ( f ∘ inl-coproduct-Fin (succ-ℕ n) (succ-ℕ m)))
      ( product-fin-sequence-type-Commutative-Semigroup G m
        ( f ∘ inr-coproduct-Fin (succ-ℕ n) (succ-ℕ m)))
  split-product-fin-sequence-type-Commutative-Semigroup G =
    split-product-fin-sequence-type-Semigroup
      ( semigroup-Commutative-Semigroup G)
```

### Permutations preserve products

```agda
module _
  {l : Level} (G : Commutative-Semigroup l)
  where

  abstract
    preserves-product-adjacent-transposition-fin-sequence-type-Commutative-Semigroup :
      (n : ℕ) → (k : Fin n) →
      (f : fin-sequence-type-Commutative-Semigroup G (succ-ℕ n)) →
      product-fin-sequence-type-Commutative-Semigroup G n f ＝
      product-fin-sequence-type-Commutative-Semigroup
        G n (f ∘ map-adjacent-transposition-Fin n k)
    preserves-product-adjacent-transposition-fin-sequence-type-Commutative-Semigroup
      (succ-ℕ n) (inl x) f =
      ap-mul-Commutative-Semigroup
        ( G)
        ( preserves-product-adjacent-transposition-fin-sequence-type-Commutative-Semigroup
          ( n)
          ( x)
          ( f ∘ inl-Fin (succ-ℕ n)))
        ( refl)
    preserves-product-adjacent-transposition-fin-sequence-type-Commutative-Semigroup
      (succ-ℕ (succ-ℕ n)) (inr star) f =
      right-swap-mul-Commutative-Semigroup G _ _ _
    preserves-product-adjacent-transposition-fin-sequence-type-Commutative-Semigroup
      (succ-ℕ zero-ℕ) (inr star) f =
      commutative-mul-Commutative-Semigroup G _ _

    preserves-product-list-adjacent-transpositions-fin-sequence-type-Commutative-Semigroup :
      (n : ℕ) → (L : list (Fin n)) →
      (f : fin-sequence-type-Commutative-Semigroup G (succ-ℕ n)) →
      product-fin-sequence-type-Commutative-Semigroup G n f ＝
      product-fin-sequence-type-Commutative-Semigroup
        G n (f ∘ map-permutation-list-adjacent-transpositions n L)
    preserves-product-list-adjacent-transpositions-fin-sequence-type-Commutative-Semigroup
      n nil f = refl
    preserves-product-list-adjacent-transpositions-fin-sequence-type-Commutative-Semigroup
      n (cons x L) f =
      ( preserves-product-adjacent-transposition-fin-sequence-type-Commutative-Semigroup
        ( n)
        ( x)
        ( f)) ∙
      ( preserves-product-list-adjacent-transpositions-fin-sequence-type-Commutative-Semigroup
        ( n)
        ( L)
        ( f ∘ map-adjacent-transposition-Fin n x))

    preserves-product-transposition-fin-sequence-type-Commutative-Semigroup :
      (n : ℕ) (i j : Fin (succ-ℕ n)) (neq : i ≠ j) →
      (f : fin-sequence-type-Commutative-Semigroup G (succ-ℕ n)) →
      product-fin-sequence-type-Commutative-Semigroup G n f ＝
      product-fin-sequence-type-Commutative-Semigroup
        G n (f ∘ map-transposition-Fin (succ-ℕ n) i j neq)
    preserves-product-transposition-fin-sequence-type-Commutative-Semigroup
      n i j i≠j f =
      ( preserves-product-list-adjacent-transpositions-fin-sequence-type-Commutative-Semigroup
        ( n)
        ( list-adjacent-transpositions-transposition-Fin n i j)
        ( f)) ∙
      ( ap
        ( λ g →
          product-fin-sequence-type-Commutative-Semigroup G
            ( n)
            ( f ∘ map-equiv g))
        ( eq-permutation-list-adjacent-transpositions-transposition-Fin
          ( n)
          ( i)
          ( j)
          ( i≠j)))

    preserves-product-list-transpositions-fin-sequence-type-Commutative-Semigroup :
      (n : ℕ) →
      (L : list (Σ (Fin (succ-ℕ n) × Fin (succ-ℕ n)) (ind-Σ _≠_))) →
      (f : fin-sequence-type-Commutative-Semigroup G (succ-ℕ n)) →
      product-fin-sequence-type-Commutative-Semigroup G n f ＝
      product-fin-sequence-type-Commutative-Semigroup
        G n
        ( f ∘
          map-equiv (permutation-list-standard-transpositions-Fin (succ-ℕ n) L))
    preserves-product-list-transpositions-fin-sequence-type-Commutative-Semigroup
      zero-ℕ _ f = ap f (eq-is-prop is-prop-Fin-1)
    preserves-product-list-transpositions-fin-sequence-type-Commutative-Semigroup
      (succ-ℕ n) nil f = refl
    preserves-product-list-transpositions-fin-sequence-type-Commutative-Semigroup
      (succ-ℕ n) (cons ((i , j) , i≠j) L) f =
      ( preserves-product-transposition-fin-sequence-type-Commutative-Semigroup
        ( succ-ℕ n)
        ( i)
        ( j)
        ( i≠j)
        ( f)) ∙
      ( preserves-product-list-transpositions-fin-sequence-type-Commutative-Semigroup
        ( succ-ℕ n)
        ( L)
        ( f ∘ map-transposition-Fin (succ-ℕ (succ-ℕ n)) i j i≠j))

    preserves-product-permutation-fin-sequence-type-Commutative-Semigroup :
      (n : ℕ) (σ : Permutation (succ-ℕ n)) →
      (f : fin-sequence-type-Commutative-Semigroup G (succ-ℕ n)) →
      product-fin-sequence-type-Commutative-Semigroup G n f ＝
      product-fin-sequence-type-Commutative-Semigroup G n (f ∘ map-equiv σ)
    preserves-product-permutation-fin-sequence-type-Commutative-Semigroup
      n σ f =
      ( preserves-product-list-transpositions-fin-sequence-type-Commutative-Semigroup
        ( n)
        ( list-standard-transpositions-permutation-Fin (succ-ℕ n) σ)
        ( f)) ∙
      ( ap
        ( λ τ →
          product-fin-sequence-type-Commutative-Semigroup G n (f ∘ map-equiv τ))
        ( eq-permutation-list-standard-transpositions-Fin (succ-ℕ n) σ))
```

## See also

- [Products of finite families of elements in commutative monoids](group-theory.products-of-finite-families-of-elements-commutative-monoids.md)
