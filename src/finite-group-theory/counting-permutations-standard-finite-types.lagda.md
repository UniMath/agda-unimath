# Counting permutations of standard finite types

```agda
{-# OPTIONS --lossy-unification #-}

module finite-group-theory.counting-permutations-standard-finite-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.factorials
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import finite-group-theory.permutations-standard-finite-types
open import finite-group-theory.transpositions-standard-finite-types

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equality-cartesian-product-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.maybe
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.universe-levels

open import univalent-combinatorics.cartesian-product-types
open import univalent-combinatorics.counting
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The [permutations](finite-group-theory.permutations-standard-finite-types.md) of
the [standard finite type](univalent-combinatorics.standard-finite-types.md)
with `n` elements are a [finite type](univalent-combinatorics.finite-types.md)
with `n` [factorial](elementary-number-theory.factorials.md) elements.

## Proof

### `Permutation (n + 1) ≃ Fin (n + 1) × Permutation n`

```agda
module _
  (n : ℕ)
  where

  cancel-head-Permutation :
    Permutation (succ-ℕ n) → Permutation (succ-ℕ n)
  cancel-head-Permutation σ =
    swap-permutation-Fin (succ-ℕ n) (inr star) (map-equiv σ (inr star)) ∘e σ

  abstract
    map-neg-one-cancel-head-Permutation :
      (σ : Permutation (succ-ℕ n)) →
      map-equiv (cancel-head-Permutation σ) (neg-one-Fin n) ＝ neg-one-Fin n
    map-neg-one-cancel-head-Permutation σ =
      map-swap-right-permutation-Fin
        ( succ-ℕ n)
        ( neg-one-Fin n)
        ( map-equiv σ (neg-one-Fin n))

  abstract
    is-left-map-is-left-cancel-head-Permutation :
      (σ : Permutation (succ-ℕ n)) (i : Fin (succ-ℕ n)) →
      is-left i → is-left (map-equiv (cancel-head-Permutation σ) i)
    is-left-map-is-left-cancel-head-Permutation σ (inl i) star =
      let
        σ' = cancel-head-Permutation σ
        σ'i = map-equiv σ' (inl i)
      in
        rec-coproduct
          ( id)
          ( λ is-right-σ'i →
            ex-falso
              ( neq-inl-inr
                ( is-injective-equiv
                  ( σ')
                  ( ( is-exception-is-right-Maybe σ'i is-right-σ'i) ∙
                    ( inv (map-neg-one-cancel-head-Permutation σ))))))
          ( is-left-or-is-right σ'i)

  abstract
    is-left-is-left-map-cancel-head-Permutation :
      (σ : Permutation (succ-ℕ n)) (i : Fin (succ-ℕ n)) →
      is-left (map-equiv (cancel-head-Permutation σ) i) → is-left i
    is-left-is-left-map-cancel-head-Permutation σ (inl i) _ = star
    is-left-is-left-map-cancel-head-Permutation σ (inr star) H =
      ex-falso
        ( is-not-left-is-right
          ( map-equiv (cancel-head-Permutation σ) (inr star))
          ( inv-tr is-right (map-neg-one-cancel-head-Permutation σ) star)
          ( H))

  has-same-elements-left-map-left-cancel-head-Permutation :
    (σ : Permutation (succ-ℕ n)) →
    has-same-elements-subtype
      ( is-left-Prop)
      ( is-left-Prop ∘ map-equiv (cancel-head-Permutation σ))
  has-same-elements-left-map-left-cancel-head-Permutation σ i =
    ( is-left-map-is-left-cancel-head-Permutation σ i ,
      is-left-is-left-map-cancel-head-Permutation σ i)

  left-cancel-head-Permutation :
    Permutation (succ-ℕ n) → Permutation n
  left-cancel-head-Permutation σ =
    ( equiv-left-summand) ∘e
    ( equiv-subtype-equiv
      ( cancel-head-Permutation σ)
      ( is-left-Prop)
      ( is-left-Prop)
      ( has-same-elements-left-map-left-cancel-head-Permutation σ)) ∘e
    ( inv-equiv equiv-left-summand)

  map-equiv-succ-Permutation :
    Permutation (succ-ℕ n) → Fin (succ-ℕ n) × Permutation n
  map-equiv-succ-Permutation σ =
    ( map-equiv σ (neg-one-Fin n) ,
      left-cancel-head-Permutation σ)

  map-inv-equiv-succ-Permutation :
    Fin (succ-ℕ n) × Permutation n → Permutation (succ-ℕ n)
  map-inv-equiv-succ-Permutation (k , σ) =
    ( swap-permutation-Fin (succ-ℕ n) (inr star) k) ∘e
    ( equiv-coproduct σ id-equiv)

  abstract
    pr1-is-section-map-inv-equiv-succ-Permutation :
      (x : Fin (succ-ℕ n) × Permutation n) →
      pr1 (map-equiv-succ-Permutation (map-inv-equiv-succ-Permutation x)) ＝
      pr1 x
    pr1-is-section-map-inv-equiv-succ-Permutation (k , σ) =
      map-swap-left-permutation-Fin (succ-ℕ n) (inr star) k

    pr2-is-section-map-inv-equiv-succ-Permutation' :
      (k : Fin (succ-ℕ n)) (σ : Permutation n) →
      htpy-equiv
        ( left-cancel-head-Permutation (map-inv-equiv-succ-Permutation (k , σ)))
        ( σ)
    pr2-is-section-map-inv-equiv-succ-Permutation' k σ i =
      ap
        ( ind-Σ left-is-left)
        ( eq-pair-Σ
          ( ( ap
              ( λ j →
                map-swap-permutation-Fin
                  ( succ-ℕ n)
                  ( inr star)
                  ( j)
                  ( map-swap-permutation-Fin
                    ( succ-ℕ n)
                    ( inr star)
                    ( k)
                    ( inl (map-equiv σ i))))
                ( map-swap-left-permutation-Fin (succ-ℕ n) (inr star) k)) ∙
            ( is-involution-map-swap-permutation-Fin
              ( succ-ℕ n)
              ( inr star)
              ( k)
              ( inl (map-equiv σ i))))
          ( eq-is-prop (is-prop-is-left {Y = unit} (inl (map-equiv σ i)))))

    is-section-map-inv-equiv-succ-Permutation :
      (x : Fin (succ-ℕ n) × Permutation n) →
      map-equiv-succ-Permutation (map-inv-equiv-succ-Permutation x) ＝ x
    is-section-map-inv-equiv-succ-Permutation x@(k , σ) =
      eq-pair
        ( pr1-is-section-map-inv-equiv-succ-Permutation x)
        ( eq-htpy-equiv (pr2-is-section-map-inv-equiv-succ-Permutation' k σ))

    is-retraction-map-inv-equiv-succ-Permutation' :
      (σ : Permutation (succ-ℕ n)) →
      htpy-equiv
        ( map-inv-equiv-succ-Permutation (map-equiv-succ-Permutation σ))
        ( σ)
    is-retraction-map-inv-equiv-succ-Permutation' σ (inl i) =
      let
        σ₋₁ = map-equiv σ (neg-one-Fin n)
      in
        ( ap
          ( map-swap-permutation-Fin (succ-ℕ n) (inr star) σ₋₁ ∘ pr1)
          ( is-retraction-map-inv-equiv-left-summand _)) ∙
        ( is-involution-map-swap-permutation-Fin (succ-ℕ n) (inr star) σ₋₁ _)
    is-retraction-map-inv-equiv-succ-Permutation' σ (inr star) =
      map-swap-left-permutation-Fin (succ-ℕ n) (inr star) _

    is-retraction-map-inv-equiv-succ-Permutation :
      (σ : Permutation (succ-ℕ n)) →
      map-inv-equiv-succ-Permutation (map-equiv-succ-Permutation σ) ＝ σ
    is-retraction-map-inv-equiv-succ-Permutation σ =
      eq-htpy-equiv (is-retraction-map-inv-equiv-succ-Permutation' σ)

  is-equiv-map-equiv-succ-Permutation : is-equiv map-equiv-succ-Permutation
  is-equiv-map-equiv-succ-Permutation =
    is-equiv-is-invertible
      ( map-inv-equiv-succ-Permutation)
      ( is-section-map-inv-equiv-succ-Permutation)
      ( is-retraction-map-inv-equiv-succ-Permutation)

  equiv-succ-Permutation :
    Permutation (succ-ℕ n) ≃ Fin (succ-ℕ n) × Permutation n
  equiv-succ-Permutation =
    ( map-equiv-succ-Permutation , is-equiv-map-equiv-succ-Permutation)
```

### Counting the elements of `Permutation n`

```agda
count-Permutation : (n : ℕ) → count (Permutation n)
count-Permutation 0 = count-is-contr (is-contr-equiv-is-empty id id)
count-Permutation (succ-ℕ n) =
  count-equiv
    ( inv-equiv (equiv-succ-Permutation n))
    ( count-product (count-Fin (succ-ℕ n)) (count-Permutation n))
```

### `Permutation n` is finite

```agda
finite-type-Permutation : (n : ℕ) → Finite-Type lzero
finite-type-Permutation n =
  ( Permutation n , is-finite-count (count-Permutation n))
```

### The number of elements of `Permutation n` is n

```agda
abstract
  number-of-elements-count-Permutation :
    (n : ℕ) →
    number-of-elements-count (count-Permutation n) ＝ factorial-ℕ n
  number-of-elements-count-Permutation 0 = refl
  number-of-elements-count-Permutation (succ-ℕ n) =
    ( ap-mul-ℕ refl (number-of-elements-count-Permutation n)) ∙
    ( commutative-mul-ℕ (succ-ℕ n) (factorial-ℕ n))

  number-of-elements-Permutation :
    (n : ℕ) →
    number-of-elements-Finite-Type (finite-type-Permutation n) ＝ factorial-ℕ n
  number-of-elements-Permutation n =
    ( inv (compute-number-of-elements-is-finite (count-Permutation n) _)) ∙
    ( number-of-elements-count-Permutation n)
```
