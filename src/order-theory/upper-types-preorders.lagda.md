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
```

</details>

## Idea

An **upper type** in a preorder `P` is a upwards closed subtype of `P`.

## Definition

```agda
is-upwards-closed-prop-subtype-Preorder :
  {l1 l2 : Level} (P : Preorder l1 l2) {l3 : Level}
  (S : subtype l3 (type-Preorder P)) →
  Prop (l1 ⊔ l2 ⊔ l3)
is-upwards-closed-prop-subtype-Preorder P =
  is-downwards-closed-prop-subtype-Preorder
    ( opposite-Preorder P)

is-upwards-closed-subtype-Preorder :
  {l1 l2 : Level} (P : Preorder l1 l2) {l3 : Level}
  (S : subtype l3 (type-Preorder P)) →
  UU (l1 ⊔ l2 ⊔ l3)
is-upwards-closed-subtype-Preorder P =
  is-downwards-closed-subtype-Preorder
    ( opposite-Preorder P)

upper-type-Preorder :
  {l1 l2 : Level} (l3 : Level) → Preorder l1 l2 → UU (l1 ⊔ l2 ⊔ lsuc l3)
upper-type-Preorder l3 P =
  Σ (subtype l3 (type-Preorder P))
    (is-upwards-closed-subtype-Preorder P)

module _
  {l1 l2 l3 : Level} (P : Preorder l1 l2) (L : upper-type-Preorder l3 P)
  where

  subtype-upper-type-Preorder : subtype l3 (type-Preorder P)
  subtype-upper-type-Preorder = pr1 L

  type-upper-type-Preorder : UU (l1 ⊔ l3)
  type-upper-type-Preorder = type-subtype subtype-upper-type-Preorder

  is-upwards-closed-upper-type-Preorder :
    is-upwards-closed-subtype-Preorder P (subtype-upper-type-Preorder)
  is-upwards-closed-upper-type-Preorder = pr2 L

  inclusion-upper-type-Preorder :
    type-upper-type-Preorder → type-Preorder P
  inclusion-upper-type-Preorder = pr1

  leq-upper-type-Preorder : (x y : type-upper-type-Preorder) → UU l2
  leq-upper-type-Preorder x y =
    leq-Preorder P
      ( inclusion-upper-type-Preorder x)
      ( inclusion-upper-type-Preorder y)
```
