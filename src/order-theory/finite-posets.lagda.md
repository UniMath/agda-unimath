# Finite posets

```agda
{-# OPTIONS --without-K --exact-split #-}

module order-theory.finite-posets where

open import foundation.decidable-types using (is-decidable)
open import foundation.propositions using (Prop; is-prop)
open import foundation.universe-levels using (Level; UU; _⊔_)

open import order-theory.finite-preorders using
  ( is-finite-preorder-Prop; is-finite-Preorder; is-prop-is-finite-Preorder;
    is-finite-element-is-finite-Preorder; is-decidable-leq-is-finite-Preorder)
open import order-theory.posets using
  ( Poset; preorder-Poset; element-Poset; leq-Poset)

open import univalent-combinatorics.finite-types using (is-finite)
```

## Finite Posets

We say that a poset is finite if its underlying preorder is finite.

```agda
module _
  {l1 l2 : Level} (X : Poset l1 l2)
  where

  is-finite-poset-Prop : Prop (l1 ⊔ l2)
  is-finite-poset-Prop = is-finite-preorder-Prop (preorder-Poset X)

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
