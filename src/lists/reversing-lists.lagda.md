# Reversing lists

```agda
module lists.reversing-lists where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.function-types
open import foundation.identity-types
open import foundation.universe-levels

open import lists.concatenation-lists
open import lists.flattening-lists
open import lists.functoriality-lists
open import lists.lists
```

</details>

## Idea

The reverse of a list of elements in `A` lists the elements of `A` in the
reversed order.

## Definition

```agda
reverse-list : {l : Level} {A : UU l} → list A → list A
reverse-list nil = nil
reverse-list (cons a l) = snoc (reverse-list l) a
```

## Properties

```agda
reverse-unit-list :
  {l1 : Level} {A : UU l1} (a : A) →
  reverse-list (unit-list a) ＝ unit-list a
reverse-unit-list a = refl

length-snoc-list :
  {l1 : Level} {A : UU l1} (x : list A) (a : A) →
  length-list (snoc x a) ＝ succ-ℕ (length-list x)
length-snoc-list nil a = refl
length-snoc-list (cons b x) a = ap succ-ℕ (length-snoc-list x a)

length-reverse-list :
  {l1 : Level} {A : UU l1} (x : list A) →
  length-list (reverse-list x) ＝ length-list x
length-reverse-list nil = refl
length-reverse-list (cons a x) =
  ( length-snoc-list (reverse-list x) a) ∙
  ( ap succ-ℕ (length-reverse-list x))

reverse-concat-list :
  {l1 : Level} {A : UU l1} (x y : list A) →
  reverse-list (concat-list x y) ＝ concat-list (reverse-list y) (reverse-list x)
reverse-concat-list nil y =
  inv (right-unit-law-concat-list (reverse-list y))
reverse-concat-list (cons a x) y =
  ( ap (λ t → snoc t a) (reverse-concat-list x y)) ∙
  ( ( snoc-concat-list (reverse-list y) (reverse-list x) a))

reverse-snoc-list :
  {l1 : Level} {A : UU l1} (x : list A) (a : A) →
  reverse-list (snoc x a) ＝ cons a (reverse-list x)
reverse-snoc-list nil a = refl
reverse-snoc-list (cons b x) a = ap (λ t → snoc t b) (reverse-snoc-list x a)

reverse-flatten-list :
  {l1 : Level} {A : UU l1} (x : list (list A)) →
  reverse-list (flatten-list x) ＝
  flatten-list (reverse-list (map-list reverse-list x))
reverse-flatten-list nil = refl
reverse-flatten-list (cons a x) =
  ( reverse-concat-list a (flatten-list x)) ∙
  ( ( ap (λ t → concat-list t (reverse-list a)) (reverse-flatten-list x)) ∙
    ( inv
      ( flatten-snoc-list
        ( reverse-list (map-list reverse-list x))
        ( (reverse-list a)))))

reverse-reverse-list :
  {l1 : Level} {A : UU l1} (x : list A) →
  reverse-list (reverse-list x) ＝ x
reverse-reverse-list nil = refl
reverse-reverse-list (cons a x) =
  ( reverse-snoc-list (reverse-list x) a) ∙
  ( ap (cons a) (reverse-reverse-list x))
```

```agda
head-reverse-list :
  {l1 : Level} {A : UU l1} (x : list A) →
  head-list (reverse-list x) ＝ last-element-list x
head-reverse-list nil = refl
head-reverse-list (cons a nil) = refl
head-reverse-list (cons a (cons b x)) =
  ( head-snoc-snoc-list (reverse-list x) b a) ∙
  ( head-reverse-list (cons b x))

last-element-reverse-list :
  {l1 : Level} {A : UU l1} (x : list A) →
  last-element-list (reverse-list x) ＝ head-list x
last-element-reverse-list x =
  ( inv (head-reverse-list (reverse-list x))) ∙
  ( ap head-list (reverse-reverse-list x))

tail-reverse-list :
  {l1 : Level} {A : UU l1} (x : list A) →
  tail-list (reverse-list x) ＝ reverse-list (remove-last-element-list x)
tail-reverse-list nil = refl
tail-reverse-list (cons a nil) = refl
tail-reverse-list (cons a (cons b x)) =
  ( tail-snoc-snoc-list (reverse-list x) b a) ∙
  ( ap (λ t → snoc t a) (tail-reverse-list (cons b x)))

remove-last-element-reverse-list :
  {l1 : Level} {A : UU l1} (x : list A) →
  remove-last-element-list (reverse-list x) ＝ reverse-list (tail-list x)
remove-last-element-reverse-list x =
  ( inv (reverse-reverse-list (remove-last-element-list (reverse-list x)))) ∙
  ( ( inv (ap reverse-list (tail-reverse-list (reverse-list x)))) ∙
    ( ap (reverse-list ∘ tail-list) (reverse-reverse-list x)))
```
