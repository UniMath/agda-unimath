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

## Definition

```agda
module _
  {l1 l2 : Level} (X : Preorder l1 l2)
  where

  is-chain-sub-preorder-Prop :
    {l3 : Level} (S : element-Preorder X → Prop l3) → Prop (l1 ⊔ l2 ⊔ l3)
  is-chain-sub-preorder-Prop S = is-total-preorder-Prop (sub-Preorder X S)

  is-chain-sub-Preorder :
    {l3 : Level} (S : element-Preorder X → Prop l3) → UU (l1 ⊔ l2 ⊔ l3)
  is-chain-sub-Preorder S = type-Prop (is-chain-sub-preorder-Prop S)

  is-prop-is-chain-sub-Preorder :
    {l3 : Level} (S : element-Preorder X → Prop l3) →
    is-prop (is-chain-sub-Preorder S)
  is-prop-is-chain-sub-Preorder S =
    is-prop-type-Prop (is-chain-sub-preorder-Prop S)

chain-Preorder :
  {l1 l2 : Level} (l : Level) (X : Preorder l1 l2) → UU (l1 ⊔ l2 ⊔ lsuc l)
chain-Preorder l X =
  Σ (element-Preorder X → Prop l) (is-chain-sub-Preorder X)

module _
  {l1 l2 l3 : Level} (X : Preorder l1 l2) (C : chain-Preorder l3 X)
  where

  sub-preorder-chain-Preorder : element-Preorder X → Prop l3
  sub-preorder-chain-Preorder = pr1 C

  element-chain-Preorder : UU (l1 ⊔ l3)
  element-chain-Preorder = type-subtype sub-preorder-chain-Preorder

module _
  {l1 l2 : Level} (X : Preorder l1 l2)
  where

  inclusion-chain-preorder-Prop :
    {l3 l4 : Level} → chain-Preorder l3 X → chain-Preorder l4 X →
    Prop (l1 ⊔ l3 ⊔ l4)
  inclusion-chain-preorder-Prop C D =
    inclusion-sub-preorder-Prop X
      ( sub-preorder-chain-Preorder X C)
      ( sub-preorder-chain-Preorder X D)

  inclusion-chain-Preorder :
    {l3 l4 : Level} → chain-Preorder l3 X → chain-Preorder l4 X →
    UU (l1 ⊔ l3 ⊔ l4)
  inclusion-chain-Preorder C D = type-Prop (inclusion-chain-preorder-Prop C D)

  is-prop-inclusion-chain-Preorder :
    {l3 l4 : Level} (C : chain-Preorder l3 X) (D : chain-Preorder l4 X) →
    is-prop (inclusion-chain-Preorder C D)
  is-prop-inclusion-chain-Preorder C D =
    is-prop-type-Prop (inclusion-chain-preorder-Prop C D)
```
