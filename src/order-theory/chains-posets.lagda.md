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
open import order-theory.subposets
```

</details>

## Idea

A {{#concept "chain" Disambiguation="in a poset" Agda=chain-Poset}} in a
[poset](order-theory.posets.md) `P` is a [subtype](foundation-core.subtypes.md)
`S` of `P` such that the ordering of `P` restricted to `S` is
[linear](order-theory.total-orders.md).

## Definition

### The predicate on subsets of posets to be a chain

```agda
module _
  {l1 l2 l3 : Level} (X : Poset l1 l2) (S : Subposet l3 X)
  where

  is-chain-prop-Subposet : Prop (l1 ⊔ l2 ⊔ l3)
  is-chain-prop-Subposet = is-chain-prop-Subpreorder (preorder-Poset X) S

  is-chain-Subposet : UU (l1 ⊔ l2 ⊔ l3)
  is-chain-Subposet = is-chain-Subpreorder (preorder-Poset X) S

  is-prop-is-chain-Subposet : is-prop is-chain-Subposet
  is-prop-is-chain-Subposet = is-prop-is-chain-Subpreorder (preorder-Poset X) S
```

### Chains in posets

```agda
chain-Poset :
  {l1 l2 : Level} (l : Level) (X : Poset l1 l2) → UU (l1 ⊔ l2 ⊔ lsuc l)
chain-Poset l X = chain-Preorder l (preorder-Poset X)

module _
  {l1 l2 l3 : Level} (X : Poset l1 l2) (C : chain-Poset l3 X)
  where

  subposet-chain-Poset : Subposet l3 X
  subposet-chain-Poset =
    subpreorder-chain-Preorder (preorder-Poset X) C

  is-chain-subposet-chain-Poset :
    is-chain-Subposet X subposet-chain-Poset
  is-chain-subposet-chain-Poset =
    is-chain-subpreorder-chain-Preorder (preorder-Poset X) C

  type-chain-Poset : UU (l1 ⊔ l3)
  type-chain-Poset = type-chain-Preorder (preorder-Poset X) C

  inclusion-type-chain-Poset : type-chain-Poset → type-Poset X
  inclusion-type-chain-Poset =
    inclusion-subpreorder-chain-Preorder (preorder-Poset X) C

module _
  {l1 l2 l3 l4 : Level} (X : Poset l1 l2)
  (C : chain-Poset l3 X) (D : chain-Poset l4 X)
  where

  inclusion-chain-prop-Poset : Prop (l1 ⊔ l3 ⊔ l4)
  inclusion-chain-prop-Poset =
    inclusion-prop-chain-Preorder (preorder-Poset X) C D

  inclusion-chain-Poset : UU (l1 ⊔ l3 ⊔ l4)
  inclusion-chain-Poset = inclusion-chain-Preorder (preorder-Poset X) C D

  is-prop-inclusion-chain-Poset : is-prop inclusion-chain-Poset
  is-prop-inclusion-chain-Poset =
    is-prop-inclusion-chain-Preorder (preorder-Poset X) C D
```

## External links

- [chain#in order theory](https://ncatlab.org/nlab/show/chain#in_order_theory)
  at $n$Lab
