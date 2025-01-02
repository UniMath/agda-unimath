# Multiplication of the elements of a list of natural numbers

```agda
module elementary-number-theory.multiplication-lists-of-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import finite-group-theory.permutations-standard-finite-types

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types

open import lists.concatenation-lists
open import lists.lists
open import lists.permutation-lists
open import lists.universal-quantification-lists
```

</details>

## Idea

Given a list of natural number `l`, we define the product of the element of the
list.

## Definition

```agda
mul-list-ℕ :
  list ℕ → ℕ
mul-list-ℕ = fold-list 1 mul-ℕ
```

## Properties

### The product of any list of natural numbers greater than one is greater than one

```agda
leq-one-mul-list-ℕ :
  (l : list ℕ) (H : for-all-list l (leq-ℕ 1)) → 1 ≤-ℕ mul-list-ℕ l
leq-one-mul-list-ℕ nil H = refl-leq-ℕ 1
leq-one-mul-list-ℕ (cons n l) (H , K) =
  preserves-order-mul-ℕ 1 n 1 (mul-list-ℕ l) H (leq-one-mul-list-ℕ l K)
```

### `mul-list-ℕ` is invariant by permutation

```agda
invariant-permutation-mul-list-ℕ :
  (l : list ℕ) (t : Permutation (length-list l)) →
  mul-list-ℕ l ＝ mul-list-ℕ (permute-list l t)
invariant-permutation-mul-list-ℕ =
  invariant-permutation-fold-list
    ( 1)
    ( mul-ℕ)
    ( λ a1 a2 b →
      ( inv (associative-mul-ℕ a1 a2 b) ∙
        ( ap (λ n → n *ℕ b) (commutative-mul-ℕ a1 a2) ∙
          ( associative-mul-ℕ a2 a1 b))))
```

### `mul-list-ℕ` of a concatenation of lists

```agda
eq-mul-list-concat-list-ℕ :
  (p q : list ℕ) →
  (mul-list-ℕ (concat-list p q)) ＝ (mul-list-ℕ p) *ℕ (mul-list-ℕ q)
eq-mul-list-concat-list-ℕ nil q = inv (left-unit-law-add-ℕ (mul-list-ℕ q))
eq-mul-list-concat-list-ℕ (cons x p) q =
  ap (mul-ℕ x) (eq-mul-list-concat-list-ℕ p q) ∙
  inv (associative-mul-ℕ x (mul-list-ℕ p) (mul-list-ℕ q))
```
