# Flattening of lists

```agda
module lists.flattening-lists where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.sums-of-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.identity-types
open import foundation.universe-levels

open import lists.concatenation-lists
open import lists.functoriality-lists
open import lists.lists
```

</details>

## Idea

Any list of lists of elements of `A` can be flattened to form a list of elements
of `A`

## Definition

```agda
flatten-list : {l : Level} {A : UU l} → list (list A) → list A
flatten-list = fold-list nil concat-list
```

## Properties

### Properties of flattening

```agda
flatten-unit-list :
  {l1 : Level} {A : UU l1} (x : list A) →
  flatten-list (unit-list x) ＝ x
flatten-unit-list x = right-unit-law-concat-list x

length-flatten-list :
  {l1 : Level} {A : UU l1} (x : list (list A)) →
  length-list (flatten-list x) ＝ sum-list-ℕ (map-list length-list x)
length-flatten-list nil = refl
length-flatten-list (cons a x) =
  ( length-concat-list a (flatten-list x)) ∙
  ( ap ((length-list a) +ℕ_) (length-flatten-list x))

flatten-concat-list :
  {l1 : Level} {A : UU l1} (x y : list (list A)) →
  flatten-list (concat-list x y) ＝ concat-list (flatten-list x) (flatten-list y)
flatten-concat-list nil y = refl
flatten-concat-list (cons a x) y =
  ( ap (concat-list a) (flatten-concat-list x y)) ∙
  ( inv (associative-concat-list a (flatten-list x) (flatten-list y)))

flatten-flatten-list :
  {l1 : Level} {A : UU l1} (x : list (list (list A))) →
  flatten-list (flatten-list x) ＝ flatten-list (map-list flatten-list x)
flatten-flatten-list nil = refl
flatten-flatten-list (cons a x) =
  ( flatten-concat-list a (flatten-list x)) ∙
  ( ap (concat-list (flatten-list a)) (flatten-flatten-list x))

flatten-snoc-list :
  {l1 : Level} {A : UU l1} (x : list (list A)) (a : list A) →
  flatten-list (snoc x a) ＝ concat-list (flatten-list x) a
flatten-snoc-list nil a = right-unit-law-concat-list a
flatten-snoc-list (cons b x) a =
  ( ap (concat-list b) (flatten-snoc-list x a)) ∙
  ( inv (associative-concat-list b (flatten-list x) a))
```
