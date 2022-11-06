# Maximal chains in preorders

```agda
{-# OPTIONS --without-K --exact-split #-}

module order-theory.maximal-chains-preorders where

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.propositions using
  ( Prop; type-Prop; is-prop-type-Prop; is-prop; Π-Prop)
open import foundation.universe-levels using (Level; UU; _⊔_; lsuc)

open import order-theory.chains-preorders using
  ( chain-Preorder; inclusion-chain-preorder-Prop; element-chain-Preorder)
open import order-theory.preorders using (Preorder)
```

## Definition

```agda

module _
  {l1 l2 : Level} (X : Preorder l1 l2)
  where
  
  is-maximal-chain-preorder-Prop :
    {l3 : Level} → chain-Preorder l3 X → Prop (l1 ⊔ l2 ⊔ lsuc l3)
  is-maximal-chain-preorder-Prop {l3} C =
    Π-Prop (chain-Preorder l3 X) (inclusion-chain-preorder-Prop X C)

  is-maximal-chain-Preorder :
    {l3 : Level} → chain-Preorder l3 X → UU (l1 ⊔ l2 ⊔ lsuc l3)
  is-maximal-chain-Preorder C = type-Prop (is-maximal-chain-preorder-Prop C)

  is-prop-is-maximal-chain-Preorder :
    {l3 : Level} (C : chain-Preorder l3 X) →
    is-prop (is-maximal-chain-Preorder C)
  is-prop-is-maximal-chain-Preorder C =
    is-prop-type-Prop (is-maximal-chain-preorder-Prop C)

maximal-chain-Preorder :
  {l1 l2 : Level} (l3 : Level) (X : Preorder l1 l2) → UU (l1 ⊔ l2 ⊔ lsuc l3)
maximal-chain-Preorder l3 X =
  Σ (chain-Preorder l3 X) (is-maximal-chain-Preorder X)

module _
  {l1 l2 l3 : Level} (X : Preorder l1 l2) (C : maximal-chain-Preorder l3 X)
  where

  chain-maximal-chain-Preorder : chain-Preorder l3 X
  chain-maximal-chain-Preorder = pr1 C

  is-maximal-chain-maximal-chain-Preorder :
    is-maximal-chain-Preorder X chain-maximal-chain-Preorder
  is-maximal-chain-maximal-chain-Preorder = pr2 C

  element-maximal-chain-Preorder : UU (l1 ⊔ l3)
  element-maximal-chain-Preorder =
    element-chain-Preorder X chain-maximal-chain-Preorder
```
