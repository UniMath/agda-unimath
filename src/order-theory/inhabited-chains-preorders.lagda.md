# Inhabited chains in preorders

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module order-theory.inhabited-chains-preorders
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions funext
open import foundation.inhabited-subtypes funext univalence truncations
open import foundation.propositions funext univalence
open import foundation.subtypes funext univalence truncations
open import foundation.universe-levels

open import order-theory.chains-preorders funext univalence truncations
open import order-theory.preorders funext univalence truncations
open import order-theory.subpreorders funext univalence truncations
open import order-theory.total-preorders funext univalence truncations
```

</details>

## Idea

An
{{#concept "inhabited chain" Disambiguation="in a preorder" Agda=inhabited-chain-Preorder}}
in a [preorder](order-theory.preorders.md) `P` is a
[subtype](foundation-core.subtypes.md) `S` of `P` such that the ordering of `P`
restricted to `S` is [linear](order-theory.total-preorders.md) and
[inhabited](foundation.inhabited-types.md).

## Definitions

### The predicate on chains in preorders of being inhabited

```agda
module _
  {l1 l2 l3 : Level} (X : Preorder l1 l2) (S : chain-Preorder l3 X)
  where

  is-inhabited-prop-chain-Preorder : Prop (l1 ⊔ l3)
  is-inhabited-prop-chain-Preorder =
    is-inhabited-subtype-Prop (subpreorder-chain-Preorder X S)

  is-inhabited-chain-Preorder : UU (l1 ⊔ l3)
  is-inhabited-chain-Preorder =
    type-Prop is-inhabited-prop-chain-Preorder

  is-prop-is-inhabited-chain-Preorder :
    is-prop is-inhabited-chain-Preorder
  is-prop-is-inhabited-chain-Preorder =
    is-prop-type-Prop is-inhabited-prop-chain-Preorder
```

### Inhabited chains in preorders

```agda
inhabited-chain-Preorder :
  {l1 l2 : Level} (l : Level) (X : Preorder l1 l2) → UU (l1 ⊔ l2 ⊔ lsuc l)
inhabited-chain-Preorder l X =
  Σ (chain-Preorder l X) (is-inhabited-chain-Preorder X)

module _
  {l1 l2 l3 : Level} (X : Preorder l1 l2) (C : inhabited-chain-Preorder l3 X)
  where

  chain-inhabited-chain-Preorder : chain-Preorder l3 X
  chain-inhabited-chain-Preorder = pr1 C

  subpreorder-inhabited-chain-Preorder : Subpreorder l3 X
  subpreorder-inhabited-chain-Preorder =
    subpreorder-chain-Preorder X chain-inhabited-chain-Preorder

  is-chain-inhabited-chain-Preorder :
    is-chain-Subpreorder X subpreorder-inhabited-chain-Preorder
  is-chain-inhabited-chain-Preorder =
    is-chain-subpreorder-chain-Preorder X chain-inhabited-chain-Preorder

  is-inhabited-inhabited-chain-Preorder :
    is-inhabited-chain-Preorder X chain-inhabited-chain-Preorder
  is-inhabited-inhabited-chain-Preorder = pr2 C

  type-inhabited-chain-Preorder : UU (l1 ⊔ l3)
  type-inhabited-chain-Preorder =
    type-subtype subpreorder-inhabited-chain-Preorder

  inclusion-subpreorder-inhabited-chain-Preorder :
    type-inhabited-chain-Preorder → type-Preorder X
  inclusion-subpreorder-inhabited-chain-Preorder =
    inclusion-subtype subpreorder-inhabited-chain-Preorder

module _
  {l1 l2 l3 l4 : Level} (X : Preorder l1 l2)
  (C : inhabited-chain-Preorder l3 X) (D : inhabited-chain-Preorder l4 X)
  where

  inclusion-prop-inhabited-chain-Preorder : Prop (l1 ⊔ l3 ⊔ l4)
  inclusion-prop-inhabited-chain-Preorder =
    inclusion-prop-chain-Preorder X
      ( chain-inhabited-chain-Preorder X C)
      ( chain-inhabited-chain-Preorder X D)

  inclusion-inhabited-chain-Preorder : UU (l1 ⊔ l3 ⊔ l4)
  inclusion-inhabited-chain-Preorder =
    type-Prop inclusion-prop-inhabited-chain-Preorder

  is-prop-inclusion-inhabited-chain-Preorder :
    is-prop inclusion-inhabited-chain-Preorder
  is-prop-inclusion-inhabited-chain-Preorder =
    is-prop-type-Prop inclusion-prop-inhabited-chain-Preorder
```
