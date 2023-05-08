# Maximal chains in posets

```agda
module order-theory.maximal-chains-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.chains-posets
open import order-theory.maximal-chains-preorders
open import order-theory.posets
```

</details>

## Idea

A **maximal chain** in a poset `P` is a chain `C` in `P` such that for any chain
`D` we have `C ⊆ D ⇒ C ＝ D`.

## Definition

```agda
module _
  {l1 l2 : Level} (X : Poset l1 l2)
  where

  is-maximal-chain-Poset-Prop :
    {l3 : Level} → chain-Poset l3 X → Prop (l1 ⊔ l2 ⊔ lsuc l3)
  is-maximal-chain-Poset-Prop =
    is-maximal-chain-Preorder-Prop (preorder-Poset X)

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

  type-maximal-chain-Poset : UU (l1 ⊔ l3)
  type-maximal-chain-Poset =
    type-maximal-chain-Preorder (preorder-Poset X) C
```
