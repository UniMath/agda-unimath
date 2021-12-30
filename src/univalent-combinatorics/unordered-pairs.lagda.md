---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module univalent-combinatorics.unordered-pairs where

open import univalent-foundations public

unordered-pair : {l : Level} (A : UU l) → UU (lsuc lzero ⊔ l)
unordered-pair A = Σ (UU-Fin two-ℕ) (λ X → pr1 X → A)

type-unordered-pair : {l : Level} {A : UU l} → unordered-pair A → UU lzero
type-unordered-pair p = pr1 (pr1 p)

has-two-elements-type-unordered-pair :
  {l : Level} {A : UU l} (p : unordered-pair A) →
  mere-equiv (Fin two-ℕ) (type-unordered-pair p)
has-two-elements-type-unordered-pair p = pr2 (pr1 p)

pair-unordered-pair :
  {l : Level} {A : UU l} (p : unordered-pair A) →
  type-unordered-pair p → A
pair-unordered-pair p = pr2 p

is-in-unordered-pair :
  {l : Level} {A : UU l} (p : unordered-pair A) (a : A) → UU l
is-in-unordered-pair p a = ∃ (λ x → Id (pair-unordered-pair p x) a)

is-selfpairing-unordered-pair :
  {l : Level} {A : UU l} (p : unordered-pair A) → UU l
is-selfpairing-unordered-pair p =
  (x y : type-unordered-pair p) →
  type-trunc-Prop (Id (pair-unordered-pair p x) (pair-unordered-pair p y))
```
