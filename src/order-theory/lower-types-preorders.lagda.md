# Lower types in preorders

```agda
module order-theory.lower-types-preorders where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.preorders
open import order-theory.subpreorders
```

</details>

## Idea

A
{{#concept "lower type" Disambiguation="in a preorder" Agda=lower-type-Preorder}}
in a [preorder](order-theory.preorders.md) is a downwards closed
[subpreorder](order-theory.subpreorders.md).

## Definition

```agda
module _
  {l1 l2 l3 : Level} (P : Preorder l1 l2) (S : Subpreorder l3 P)
  where

  is-downwards-closed-prop-Subpreorder : Prop (l1 ⊔ l2 ⊔ l3)
  is-downwards-closed-prop-Subpreorder =
    Π-Prop
      ( type-Preorder P)
      ( λ x →
        Π-Prop
          ( type-Preorder P)
          ( λ y → leq-prop-Preorder P y x ⇒ S x ⇒ S y))

  is-downwards-closed-Subpreorder : UU (l1 ⊔ l2 ⊔ l3)
  is-downwards-closed-Subpreorder =
    type-Prop is-downwards-closed-prop-Subpreorder

lower-type-Preorder :
  {l1 l2 : Level} (l3 : Level) → Preorder l1 l2 → UU (l1 ⊔ l2 ⊔ lsuc l3)
lower-type-Preorder l3 P =
  Σ (Subpreorder l3 P) (is-downwards-closed-Subpreorder P)

module _
  {l1 l2 l3 : Level} (P : Preorder l1 l2) (L : lower-type-Preorder l3 P)
  where

  subtype-lower-type-Preorder : Subpreorder l3 P
  subtype-lower-type-Preorder = pr1 L

  type-lower-type-Preorder : UU (l1 ⊔ l3)
  type-lower-type-Preorder = type-subtype subtype-lower-type-Preorder

  is-downwards-closed-lower-type-Preorder :
    is-downwards-closed-Subpreorder P subtype-lower-type-Preorder
  is-downwards-closed-lower-type-Preorder = pr2 L

  inclusion-lower-type-Preorder :
    type-lower-type-Preorder → type-Preorder P
  inclusion-lower-type-Preorder = pr1

  leq-lower-type-Preorder : (x y : type-lower-type-Preorder) → UU l2
  leq-lower-type-Preorder = leq-Subpreorder P subtype-lower-type-Preorder
```
