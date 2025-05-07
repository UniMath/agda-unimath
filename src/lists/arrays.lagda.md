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

open import lists.equivalence-tuples-finite-sequences
open import lists.finite-sequences
open import lists.lists
open import lists.tuples

open import univalent-combinatorics.involution-standard-finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

An array is a pair of a natural number `n`, and a
[finite sequence](lists.finite-sequences.md) of elements of the type `A`. We
show that arrays and lists are equivalent.

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

### The definition of `fold-tuple`

```agda
fold-tuple :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (b : B) (μ : A → (B → B)) →
  {n : ℕ} → tuple A n → B
fold-tuple b μ {0} _ = b
fold-tuple b μ (a ∷ l) = μ a (fold-tuple b μ l)
```

## Properties

### The types of lists and arrays are equivalent

```agda
module _
  {l : Level} {A : UU l}
  where

  list-tuple : (n : ℕ) → (tuple A n) → list A
  list-tuple zero-ℕ _ = nil
  list-tuple (succ-ℕ n) (x ∷ l) = cons x (list-tuple n l)

  tuple-list : (l : list A) → tuple A (length-list l)
  tuple-list nil = empty-tuple
  tuple-list (cons x l) = x ∷ tuple-list l

  is-section-tuple-list : (λ l → list-tuple (length-list l) (tuple-list l)) ~ id
  is-section-tuple-list nil = refl
  is-section-tuple-list (cons x l) = ap (cons x) (is-section-tuple-list l)

  is-retraction-tuple-list :
    ( λ (x : Σ ℕ (λ n → tuple A n)) →
      ( length-list (list-tuple (pr1 x) (pr2 x)) ,
        tuple-list (list-tuple (pr1 x) (pr2 x)))) ~
    id
  is-retraction-tuple-list (zero-ℕ , empty-tuple) = refl
  is-retraction-tuple-list (succ-ℕ n , (x ∷ v)) =
    ap
      ( λ v → succ-ℕ (pr1 v) , (x ∷ (pr2 v)))
      ( is-retraction-tuple-list (n , v))

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

### An element `x` is in a tuple `v` iff it is in `list-tuple n v`

```agda
  is-in-list-is-in-tuple-list :
    (l : list A) (x : A) →
    x ∈-tuple (tuple-list l) → x ∈-list l
  is-in-list-is-in-tuple-list (cons y l) .y (is-head .y .(tuple-list l)) =
    is-head y l
  is-in-list-is-in-tuple-list
    (cons y l) x (is-in-tail .x .y .(tuple-list l) I) =
    is-in-tail x y l (is-in-list-is-in-tuple-list l x I)

  is-in-tuple-list-is-in-list :
    (l : list A) (x : A) →
    x ∈-list l → x ∈-tuple (tuple-list l)
  is-in-tuple-list-is-in-list (cons x l) x (is-head .x l) =
    is-head x (tuple-list l)
  is-in-tuple-list-is-in-list (cons y l) x (is-in-tail .x .y l I) =
    is-in-tail x y (tuple-list l) (is-in-tuple-list-is-in-list l x I)
```

### Link between `fold-list` and `fold-tuple`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (b : B)
  (μ : A → (B → B))
  where
  htpy-fold-list-fold-tuple :
    (l : list A) →
    fold-tuple b μ (tuple-list l) ＝ fold-list b μ l
  htpy-fold-list-fold-tuple nil = refl
  htpy-fold-list-fold-tuple (cons x l) =
    ap (μ x) (htpy-fold-list-fold-tuple l)
```
