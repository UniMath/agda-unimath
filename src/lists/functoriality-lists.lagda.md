# Functoriality of the list operation

```agda
module lists.functoriality-lists where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.functions
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import lists.concatenation-lists
open import lists.lists
```

</details>

## Idea

Given a functiion `f : A → B`, we obtain a function
`map-list f : list A → list B`.

## Definition

```agda
map-list :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  list A → list B
map-list f = fold-list nil (λ a → cons (f a))
```

## Property

### `map-list` preserves the length of a list

```agda
length-map-list :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (l : list A) →
  Id (length-list (map-list f l)) (length-list l)
length-map-list f nil = refl
length-map-list f (cons x l) =
  ap succ-ℕ (length-map-list f l)
```

### `map-list` preserves concatenation

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  preserves-concat-map-list :
    (l k : list A) →
    Id ( map-list f (concat-list l k))
       ( concat-list (map-list f l) (map-list f k))
  preserves-concat-map-list nil k = refl
  preserves-concat-map-list (cons x l) k =
    ap (cons (f x)) (preserves-concat-map-list l k)
```

### Functoriality of the list operation

First we introduce the functoriality of the list operation, because it will come
in handy when we try to define and prove more advanced things.

```agda
identity-law-map-list :
  {l1 : Level} {A : UU l1} →
  map-list (id {A = A}) ~ id
identity-law-map-list nil = refl
identity-law-map-list (cons a x) =
  ap (cons a) (identity-law-map-list x)

composition-law-map-list :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} →
  (f : A → B) (g : B → C) →
  map-list (g ∘ f) ~ (map-list g ∘ map-list f)
composition-law-map-list f g nil = refl
composition-law-map-list f g (cons a x) =
  ap (cons (g (f a))) (composition-law-map-list f g x)
```

### `map-list` applied to lists of the form `snoc x a`

```agda
map-snoc-list :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (x : list A) (a : A) →
  map-list f (snoc x a) ＝ snoc (map-list f x) (f a)
map-snoc-list f nil a = refl
map-snoc-list f (cons b x) a = ap (cons (f b)) (map-snoc-list f x a)
```
