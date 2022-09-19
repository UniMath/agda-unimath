# Totally ordered posets

```agda
{-# OPTIONS --without-K --exact-split #-}

module order-theory.total-posets where

open import foundation.propositions using (Prop; is-prop)
open import foundation.universe-levels using (Level; UU; _⊔_)

open import order-theory.posets using  (Poset; element-Poset; preorder-Poset)
open import order-theory.total-preorders using
  ( incident-preorder-Prop; incident-Preorder; is-prop-incident-Preorder;
    is-total-preorder-Prop; is-total-Preorder; is-prop-is-total-Preorder)
```

## Definition

```agda
module _
  {l1 l2 : Level} (X : Poset l1 l2)
  where

  incident-poset-Prop : (x y : element-Poset X) → Prop l2
  incident-poset-Prop = incident-preorder-Prop (preorder-Poset X)

  incident-Poset : (x y : element-Poset X) → UU l2
  incident-Poset = incident-Preorder (preorder-Poset X)

  is-prop-incident-Poset :
    (x y : element-Poset X) → is-prop (incident-Poset x y)
  is-prop-incident-Poset = is-prop-incident-Preorder (preorder-Poset X)

  is-total-poset-Prop : Prop (l1 ⊔ l2)
  is-total-poset-Prop = is-total-preorder-Prop (preorder-Poset X)

  is-total-Poset : UU (l1 ⊔ l2)
  is-total-Poset = is-total-Preorder (preorder-Poset X)

  is-prop-is-total-Poset : is-prop is-total-Poset
  is-prop-is-total-Poset = is-prop-is-total-Preorder (preorder-Poset X)
```
