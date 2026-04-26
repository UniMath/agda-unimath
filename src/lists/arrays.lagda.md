# Arrays

```agda
module lists.arrays where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.unit-type
open import foundation.universe-levels

open import linear-algebra.vectors

open import lists.elementhood-relation-lists
open import lists.equivalence-tuples-finite-sequences
open import lists.finite-sequences
open import lists.lists
open import lists.tuples

open import univalent-combinatorics.involution-standard-finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

An
{{#concept "array" WD="array data type" WDID=Q121079 WD="list" WDID=Q27948 Agda=array}}
is a [pair](foundation.dependent-pair-types.md) consisting of a [natural number](elementary-number-theory.natural-numbers.md) `n`, and a [finite sequence](lists.finite-sequences.md) of `n` elements of `A`. The concept of array is [equivalent](foundation-core.equivalences.md) to the concept of [list](lists.lists.md).

## Definitions

### Arrays

```agda
array : {l : Level} → UU l → UU l
array A = Σ ℕ (λ n → fin-sequence A n)

module _
  {l : Level} {A : UU l}
  where

  length-array : array A → ℕ
  length-array = pr1

  fin-sequence-array : (t : array A) → Fin (length-array t) → A
  fin-sequence-array = pr2

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
      rec-coproduct (fin-sequence-array t) (λ _ → a))

  revert-array : array A → array A
  revert-array (n , t) = (n , λ k → t (opposite-Fin n k))
```

## Properties

```agda
module _
  {l : Level} {A : UU l}
  where

  list-array : array A → list A
  list-array (n , t) = list-tuple n (tuple-fin-sequence n t)

  array-list : list A → array A
  array-list l =
    ( length-list l , fin-sequence-tuple (length-list l) (tuple-list l))

  is-section-array-list : (list-array ∘ array-list) ~ id
  is-section-array-list nil = refl
  is-section-array-list (cons x l) = ap (cons x) (is-section-array-list l)

  is-retraction-array-list : (array-list ∘ list-array) ~ id
  is-retraction-array-list (n , t) =
    ap
      ( λ (n , v) → (n , fin-sequence-tuple n v))
      ( is-retraction-tuple-list (n , tuple-fin-sequence n t)) ∙
    eq-pair-eq-fiber (is-retraction-fin-sequence-tuple n t)

  equiv-list-array : array A ≃ list A
  pr1 equiv-list-array = list-array
  pr2 equiv-list-array =
    is-equiv-is-invertible
      array-list
      is-section-array-list
      is-retraction-array-list

  equiv-array-list : list A ≃ array A
  pr1 equiv-array-list = array-list
  pr2 equiv-array-list =
    is-equiv-is-invertible
      list-array
      is-retraction-array-list
      is-section-array-list
```

### Computational rules of the equivalence between arrays and lists

```agda
  compute-length-list-list-tuple :
    (n : ℕ) (v : tuple A n) →
    length-list (list-tuple n v) ＝ n
  compute-length-list-list-tuple zero-ℕ v = refl
  compute-length-list-list-tuple (succ-ℕ n) (x ∷ v) =
    ap succ-ℕ (compute-length-list-list-tuple n v)

  compute-length-list-list-array :
    (t : array A) → length-list (list-array t) ＝ length-array t
  compute-length-list-list-array t =
    compute-length-list-list-tuple
      ( length-array t)
      ( tuple-fin-sequence
        ( length-array t)
        ( fin-sequence-array t))
```
