# Chains in posets

```agda
module order-theory.chains-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.chains-preorders
open import order-theory.posets
```

</details>

## Idea

A {{#concept "chain" Disambiguation="in a poset" Agda=chain-Poset}} in a
[poset](order-theory.posets.md) `P` is a [subtype](foundation-core.subtypes.md)
`S` of `P` such that the ordering of `P` restricted to `S` is
[linear](order-theory.total-orders.md).

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

  is-chain-Subposet-chain-Poset :
    is-chain-Subposet X sub-preorder-chain-Poset
  is-chain-Subposet-chain-Poset =
    is-chain-Subpreorder-chain-Preorder (preorder-Poset X) C

  type-chain-Poset : UU (l1 ⊔ l3)
  type-chain-Poset = type-chain-Preorder (preorder-Poset X) C

  type-Poset-type-chain-Poset : type-chain-Poset → type-Poset X
  type-Poset-type-chain-Poset =
    type-Preorder-type-chain-Preorder (preorder-Poset X) C

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

## External links

- [chain#in order theory](https://ncatlab.org/nlab/show/chain#in_order_theory)
  at $n$Lab
