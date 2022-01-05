---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module order-theory.finite-posets where

open import order-theory.posets
open import order-theory.finite-preorders public
```

## Finite Posets

We say that a poset is finite if its underlying preorder is finite.

```agda
module _
  {l1 l2 : Level} (X : Poset l1 l2)
  where

  is-finite-Poset-Prop : UU-Prop (l1 ⊔ l2)
  is-finite-Poset-Prop = is-finite-Preorder-Prop (preorder-Poset X)

  is-finite-Poset : UU (l1 ⊔ l2)
  is-finite-Poset = is-finite-Preorder (preorder-Poset X)

  is-prop-is-finite-Poset : is-prop is-finite-Poset
  is-prop-is-finite-Poset = is-prop-is-finite-Preorder (preorder-Poset X)

  is-finite-element-is-finite-Poset :
    is-finite-Poset → is-finite (element-Poset X)
  is-finite-element-is-finite-Poset =
    is-finite-element-is-finite-Preorder (preorder-Poset X)

  is-decidable-leq-is-finite-Poset :
    is-finite-Poset →
    (x y : element-Poset X) → is-decidable (leq-Poset X x y)
  is-decidable-leq-is-finite-Poset =
    is-decidable-leq-is-finite-Preorder (preorder-Poset X)
```
