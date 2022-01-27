---
title: Univalent Mathematics in Agda
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundation.lists where

open import elementary-number-theory.addition-natural-numbers using (add-ℕ)
open import foundation.functions using (id; _∘_)
open import foundation.universe-levels using (UU; Level)
open import elementary-number-theory.multiplication-natural-numbers using
  ( mul-ℕ)
open import elementary-number-theory.natural-numbers using (ℕ; succ-ℕ)
```

```agda
data list {l : Level} (A : UU l) : UU l where
  nil : list A
  cons : A → list A → list A

in-list : {l : Level} {A : UU l} → A → list A
in-list a = cons a nil
```

## Operations on lists

```agda
fold-list :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (b : B) (μ : A → (B → B)) →
  list A → B
fold-list b μ nil = b
fold-list b μ (cons a l) = μ a (fold-list b μ l)

length-list : {l : Level} {A : UU l} → list A → ℕ
length-list = fold-list 0 (λ a → succ-ℕ)

sum-list-ℕ : list ℕ → ℕ
sum-list-ℕ = fold-list 0 add-ℕ

product-list-ℕ : list ℕ → ℕ
product-list-ℕ = fold-list 1 mul-ℕ

concat-list : {l : Level} {A : UU l} → list A → (list A → list A)
concat-list {l} {A} = fold-list id (λ a f → (cons a) ∘ f)

flatten-list : {l : Level} {A : UU l} → list (list A) → list A
flatten-list = fold-list nil concat-list

reverse-list : {l : Level} {A : UU l} → list A → list A
reverse-list nil = nil
reverse-list (cons a l) = concat-list (reverse-list l) (in-list a)
```
