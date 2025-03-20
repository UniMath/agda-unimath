# Lower types in preorders

```agda
open import foundation.function-extensionality-axiom

module
  order-theory.lower-types-preorders
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.subtypes funext
open import foundation.universe-levels

open import order-theory.preorders funext
```

</details>

## Idea

A **lower type** in a preorder `P` is a downwards closed subtype of `P`.

## Definition

```agda
module _
  {l1 l2 : Level} (P : Preorder l1 l2)
  where

  is-downwards-closed-subtype-Preorder :
    {l3 : Level} (S : subtype l3 (type-Preorder P)) → UU (l1 ⊔ l2 ⊔ l3)
  is-downwards-closed-subtype-Preorder S =
    (x y : type-Preorder P) →
    leq-Preorder P y x → is-in-subtype S x → is-in-subtype S y

lower-type-Preorder :
  {l1 l2 : Level} (l3 : Level) → Preorder l1 l2 → UU (l1 ⊔ l2 ⊔ lsuc l3)
lower-type-Preorder l3 P =
  Σ (subtype l3 (type-Preorder P)) (is-downwards-closed-subtype-Preorder P)

module _
  {l1 l2 l3 : Level} (P : Preorder l1 l2) (L : lower-type-Preorder l3 P)
  where

  subtype-lower-type-Preorder : subtype l3 (type-Preorder P)
  subtype-lower-type-Preorder = pr1 L

  type-lower-type-Preorder : UU (l1 ⊔ l3)
  type-lower-type-Preorder = type-subtype subtype-lower-type-Preorder

  inclusion-lower-type-Preorder :
    type-lower-type-Preorder → type-Preorder P
  inclusion-lower-type-Preorder = pr1

  leq-lower-type-Preorder : (x y : type-lower-type-Preorder) → UU l2
  leq-lower-type-Preorder x y =
    leq-Preorder P
      ( inclusion-lower-type-Preorder x)
      ( inclusion-lower-type-Preorder y)
```
