# Maximal chains in preorders

```agda
open import foundation.function-extensionality-axiom

module
  order-theory.maximal-chains-preorders
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.propositions funext
open import foundation.universe-levels

open import order-theory.chains-preorders funext
open import order-theory.preorders funext
```

</details>

## Idea

A
{{#concept "maximal chain" Disambiguation="in a preorder" Agda=maximal-chain-Preorder}}
in a [preorder](order-theory.preorders.md) `P` is a
[chain](order-theory.chains-preorders.md) `C` in `P` such that for any chain `D`
we have `C ⊆ D ⇒ C ＝ D`.

## Definition

```agda
module _
  {l1 l2 : Level} (X : Preorder l1 l2)
  where

  is-maximal-chain-Preorder-Prop :
    {l3 : Level} → chain-Preorder l3 X → Prop (l1 ⊔ l2 ⊔ lsuc l3)
  is-maximal-chain-Preorder-Prop {l3} C =
    Π-Prop
      ( chain-Preorder l3 X)
      ( λ D →
        function-Prop
          ( inclusion-chain-Preorder X C D)
          ( inclusion-prop-chain-Preorder X D C))

  is-maximal-chain-Preorder :
    {l3 : Level} → chain-Preorder l3 X → UU (l1 ⊔ l2 ⊔ lsuc l3)
  is-maximal-chain-Preorder C = type-Prop (is-maximal-chain-Preorder-Prop C)

  is-prop-is-maximal-chain-Preorder :
    {l3 : Level} (C : chain-Preorder l3 X) →
    is-prop (is-maximal-chain-Preorder C)
  is-prop-is-maximal-chain-Preorder C =
    is-prop-type-Prop (is-maximal-chain-Preorder-Prop C)

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

  type-maximal-chain-Preorder : UU (l1 ⊔ l3)
  type-maximal-chain-Preorder =
    type-chain-Preorder X chain-maximal-chain-Preorder
```
