# Arrays

```agda
module lists.arrays where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.functions
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.unit-type
open import foundation.universal-property-coproduct-types
open import foundation.universe-levels

open import linear-algebra.vectors

open import lists.lists

open import univalent-combinatorics.involution-standard-finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

In these file, we defined the notion of array. An array is a pair of a natural
number `n`, and a function from `Fin n` to `A`. We also show that arrays and
lists are equivalent.

```agda
array : {l : Level} → UU l  → UU l
array A = Σ ℕ (λ n → functional-vec A n)

module _
  {l : Level} {A : UU l}
  where

  length-array : array A → ℕ
  length-array = pr1

  map-array : (t : array A) → Fin (length-array t) → A
  map-array = pr2

  empty-array : array A
  pr1 (empty-array) = zero-ℕ
  pr2 (empty-array) ()

  is-empty-array-Prop : array A → Prop lzero
  is-empty-array-Prop (zero-ℕ , t) = unit-Prop
  is-empty-array-Prop (succ-ℕ n , t) = empty-Prop

  is-empty-array : array A → UU lzero
  is-empty-array = type-Prop ∘ is-empty-array-Prop

  is-nonempty-array-Prop : array A → Prop lzero
  is-nonempty-array-Prop (zero-ℕ , t) = empty-Prop
  is-nonempty-array-Prop (succ-ℕ n , t) = unit-Prop

  is-nonempty-array : array A → UU lzero
  is-nonempty-array = type-Prop ∘ is-nonempty-array-Prop

  head-array : (t : array A) → is-nonempty-array t → A
  head-array (succ-ℕ n , f) _ = f (inr star)

  tail-array : (t : array A) → is-nonempty-array t → array A
  tail-array (succ-ℕ n , f) _ = n , f ∘ inl

  cons-array : A → array A → array A
  cons-array a t =
    ( succ-ℕ (length-array t) ,
      ind-coprod (λ _ → A) (map-array t) λ _ → a)

  revert-array : array A → array A
  revert-array (n , t) = (n , λ k → t (opposite-Fin n k))
```

## Properties

### The types of listed and arrays are equivalent

```agda
module _
  {l : Level} {A : UU l}
  where

  equiv-list-array : array A ≃ list A
  equiv-list-array = equiv-list-vec ∘e equiv-tot compute-vec

  equiv-array-list : list A ≃ array A
  equiv-array-list =
    equiv-tot (λ n → inv-equiv (compute-vec n)) ∘e equiv-vec-list
```
