# Chains in preorders

```agda
module order-theory.chains-preorders where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.preorders
open import order-theory.subpreorders
open import order-theory.total-preorders
```

</details>

## Idea

A {{#concept "chain" Disambiguation="in a preorder" Agda=chain-Preorder}} in a
[preorder](order-theory.preorders.md) `P` is a
[subtype](foundation-core.subtypes.md) `S` of `P` such that the ordering of `P`
restricted to `S` is [linear](order-theory.total-preorders.md).

## Definitions

### The predicate on subsets of preorders to be a chain

```agda
module _
  {l1 l2 l3 : Level} (X : Preorder l1 l2) (S : Subpreorder l3 X)
  where

  is-chain-prop-Subpreorder : Prop (l1 ⊔ l2 ⊔ l3)
  is-chain-prop-Subpreorder =
    is-total-prop-Preorder (preorder-Subpreorder X S)

  is-chain-Subpreorder : UU (l1 ⊔ l2 ⊔ l3)
  is-chain-Subpreorder = type-Prop is-chain-prop-Subpreorder

  is-prop-is-chain-Subpreorder : is-prop is-chain-Subpreorder
  is-prop-is-chain-Subpreorder = is-prop-type-Prop is-chain-prop-Subpreorder
```

### Chains in preorders

```agda
chain-Preorder :
  {l1 l2 : Level} (l : Level) (X : Preorder l1 l2) → UU (l1 ⊔ l2 ⊔ lsuc l)
chain-Preorder l X =
  Σ (type-Preorder X → Prop l) (is-chain-Subpreorder X)

module _
  {l1 l2 l3 : Level} (X : Preorder l1 l2) (C : chain-Preorder l3 X)
  where

  subpreorder-chain-Preorder : Subpreorder l3 X
  subpreorder-chain-Preorder = pr1 C

  is-chain-subpreorder-chain-Preorder :
    is-chain-Subpreorder X subpreorder-chain-Preorder
  is-chain-subpreorder-chain-Preorder = pr2 C

  type-chain-Preorder : UU (l1 ⊔ l3)
  type-chain-Preorder = type-subtype subpreorder-chain-Preorder

  inclusion-subpreorder-chain-Preorder : type-chain-Preorder → type-Preorder X
  inclusion-subpreorder-chain-Preorder =
    inclusion-subtype subpreorder-chain-Preorder

module _
  {l1 l2 l3 l4 : Level} (X : Preorder l1 l2)
  (C : chain-Preorder l3 X) (D : chain-Preorder l4 X)
  where

  inclusion-prop-chain-Preorder : Prop (l1 ⊔ l3 ⊔ l4)
  inclusion-prop-chain-Preorder =
    inclusion-prop-Subpreorder X
      ( subpreorder-chain-Preorder X C)
      ( subpreorder-chain-Preorder X D)

  inclusion-chain-Preorder : UU (l1 ⊔ l3 ⊔ l4)
  inclusion-chain-Preorder = type-Prop inclusion-prop-chain-Preorder

  is-prop-inclusion-chain-Preorder :
    is-prop inclusion-chain-Preorder
  is-prop-inclusion-chain-Preorder =
    is-prop-type-Prop inclusion-prop-chain-Preorder
```

## External links

- [Total order, chains](https://en.wikipedia.org/wiki/Total_order#Chains) at
  Wikipedia
- [chain, in order theory](https://ncatlab.org/nlab/show/chain#in_order_theory)
  at $n$Lab
