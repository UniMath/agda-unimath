# Upper types in preorders

```agda
module order-theory.upper-types-preorders where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.lower-types-preorders
open import order-theory.opposite-preorders
open import order-theory.preorders
open import order-theory.subpreorders
```

</details>

## Idea

An
{{#concept "upper type" Disambiguation="in a preorder" Agda=upper-type-Preorder}}
in a [preorder](order-theory.preorders.md) is an upwards closed
[subpreorder](order-theory.subpreorders.md), i.e. a
[lower type](order-theory.lower-types-preorders.md) in the
[opposite preorder](order-theory.opposite-preorders.md).

## Definition

```agda
is-upwards-closed-prop-Subpreorder :
  {l1 l2 l3 : Level} (P : Preorder l1 l2) (S : Subpreorder l3 P) →
  Prop (l1 ⊔ l2 ⊔ l3)
is-upwards-closed-prop-Subpreorder P =
  is-downwards-closed-prop-Subpreorder (opposite-Preorder P)

is-upwards-closed-Subpreorder :
  {l1 l2 l3 : Level} (P : Preorder l1 l2) (S : Subpreorder l3 P) →
  UU (l1 ⊔ l2 ⊔ l3)
is-upwards-closed-Subpreorder P =
  is-downwards-closed-Subpreorder (opposite-Preorder P)

upper-type-Preorder :
  {l1 l2 : Level} (l3 : Level) → Preorder l1 l2 → UU (l1 ⊔ l2 ⊔ lsuc l3)
upper-type-Preorder l3 P =
  Σ (Subpreorder l3 P) (is-upwards-closed-Subpreorder P)

module _
  {l1 l2 l3 : Level} (P : Preorder l1 l2) (L : upper-type-Preorder l3 P)
  where

  subtype-upper-type-Preorder : Subpreorder l3 P
  subtype-upper-type-Preorder = pr1 L

  type-upper-type-Preorder : UU (l1 ⊔ l3)
  type-upper-type-Preorder = type-subtype subtype-upper-type-Preorder

  is-upwards-closed-upper-type-Preorder :
    is-upwards-closed-Subpreorder P (subtype-upper-type-Preorder)
  is-upwards-closed-upper-type-Preorder = pr2 L

  inclusion-upper-type-Preorder : type-upper-type-Preorder → type-Preorder P
  inclusion-upper-type-Preorder = pr1

  leq-upper-type-Preorder : (x y : type-upper-type-Preorder) → UU l2
  leq-upper-type-Preorder = leq-Subpreorder P subtype-upper-type-Preorder
```
