# Chains in posets

```agda
module order-theory.chains-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.chains-preorders
open import order-theory.posets
```

</details>

## Idea

A **chain** in a poset `P` is a subtype `S` of `P` such that the ordering of `P`
restricted to `S` is linear.

## Definition

```agda
module _
  {l1 l2 : Level} (X : Poset l1 l2)
  where

  is-chain-Subposet-Prop :
    {l3 : Level} (S : type-Poset X → Prop l3) → Prop (l1 ⊔ l2 ⊔ l3)
  is-chain-Subposet-Prop = is-chain-Subpreorder-Prop (preorder-Poset X)

  is-chain-Subposet :
    {l3 : Level} (S : type-Poset X → Prop l3) → UU (l1 ⊔ l2 ⊔ l3)
  is-chain-Subposet = is-chain-Subpreorder (preorder-Poset X)

  is-prop-is-chain-Subposet :
    {l3 : Level} (S : type-Poset X → Prop l3) →
    is-prop (is-chain-Subposet S)
  is-prop-is-chain-Subposet = is-prop-is-chain-Subpreorder (preorder-Poset X)

chain-Poset :
  {l1 l2 : Level} (l : Level) (X : Poset l1 l2) → UU (l1 ⊔ l2 ⊔ lsuc l)
chain-Poset l X = chain-Preorder l (preorder-Poset X)

module _
  {l1 l2 l3 : Level} (X : Poset l1 l2) (C : chain-Poset l3 X)
  where

  sub-preorder-chain-Poset : type-Poset X → Prop l3
  sub-preorder-chain-Poset =
    sub-preorder-chain-Preorder (preorder-Poset X) C

  type-chain-Poset : UU (l1 ⊔ l3)
  type-chain-Poset = type-chain-Preorder (preorder-Poset X) C

module _
  {l1 l2 : Level} (X : Poset l1 l2)
  where

  inclusion-chain-Poset-Prop :
    {l3 l4 : Level} → chain-Poset l3 X → chain-Poset l4 X →
    Prop (l1 ⊔ l3 ⊔ l4)
  inclusion-chain-Poset-Prop = inclusion-chain-Preorder-Prop (preorder-Poset X)

  inclusion-chain-Poset :
    {l3 l4 : Level} → chain-Poset l3 X → chain-Poset l4 X → UU (l1 ⊔ l3 ⊔ l4)
  inclusion-chain-Poset = inclusion-chain-Preorder (preorder-Poset X)

  is-prop-inclusion-chain-Poset :
    {l3 l4 : Level} (C : chain-Poset l3 X) (D : chain-Poset l4 X) →
    is-prop (inclusion-chain-Poset C D)
  is-prop-inclusion-chain-Poset =
    is-prop-inclusion-chain-Preorder (preorder-Poset X)
```
