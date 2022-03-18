# Maximal chains in posets

```agda
{-# OPTIONS --without-K --exact-split #-}

module order-theory.maximal-chains-posets where

open import foundation.propositions using (UU-Prop; is-prop)
open import foundation.universe-levels using (Level; UU; _⊔_; lsuc)

open import order-theory.chains-posets using (chain-Poset)
open import order-theory.maximal-chains-preorders using
  ( is-maximal-chain-preorder-Prop; is-maximal-chain-Preorder;
    is-prop-is-maximal-chain-Preorder; maximal-chain-Preorder;
    chain-maximal-chain-Preorder; is-maximal-chain-maximal-chain-Preorder;
    element-maximal-chain-Preorder)
open import order-theory.posets using (Poset; preorder-Poset)
```

## Definition

```agda

module _
  {l1 l2 : Level} (X : Poset l1 l2)
  where
  
  is-maximal-chain-poset-Prop :
    {l3 : Level} → chain-Poset l3 X → UU-Prop (l1 ⊔ l2 ⊔ lsuc l3)
  is-maximal-chain-poset-Prop =
    is-maximal-chain-preorder-Prop (preorder-Poset X)

  is-maximal-chain-Poset :
    {l3 : Level} → chain-Poset l3 X → UU (l1 ⊔ l2 ⊔ lsuc l3)
  is-maximal-chain-Poset = is-maximal-chain-Preorder (preorder-Poset X)

  is-prop-is-maximal-chain-Poset :
    {l3 : Level} (C : chain-Poset l3 X) → is-prop (is-maximal-chain-Poset C)
  is-prop-is-maximal-chain-Poset =
    is-prop-is-maximal-chain-Preorder (preorder-Poset X)

maximal-chain-Poset :
  {l1 l2 : Level} (l3 : Level) (X : Poset l1 l2) → UU (l1 ⊔ l2 ⊔ lsuc l3)
maximal-chain-Poset l3 X = maximal-chain-Preorder l3 (preorder-Poset X)

module _
  {l1 l2 l3 : Level} (X : Poset l1 l2) (C : maximal-chain-Poset l3 X)
  where

  chain-maximal-chain-Poset : chain-Poset l3 X
  chain-maximal-chain-Poset = chain-maximal-chain-Preorder (preorder-Poset X) C

  is-maximal-chain-maximal-chain-Poset :
    is-maximal-chain-Poset X chain-maximal-chain-Poset
  is-maximal-chain-maximal-chain-Poset =
    is-maximal-chain-maximal-chain-Preorder (preorder-Poset X) C

  element-maximal-chain-Poset : UU (l1 ⊔ l3)
  element-maximal-chain-Poset =
    element-maximal-chain-Preorder (preorder-Poset X) C
```
