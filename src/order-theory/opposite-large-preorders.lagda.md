# Opposite large preorders

```agda
module order-theory.opposite-large-preorders where
```

<details><summary>Imports</summary>

```agda
open import order-theory.large-preorders

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.homotopies
open import foundation.identity-types
open import foundation.sets
open import foundation.large-identity-types
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

Let `X` be a [large preorder](order-theory.large-preorders.md), its
{{#concept "opposite" Disambiguation="large preorder" Agda=opposite-Large-Preorder}}
`Xᵒᵖ` is given by reversing the relation.

## Definition

### The opposite large preorder

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (P : Large-Preorder α β)
  where

  type-opposite-Large-Preorder : (l : Level) → UU (α l)
  type-opposite-Large-Preorder = type-Large-Preorder P

  leq-prop-opposite-Large-Preorder :
    {l1 l2 : Level}
    (X : type-opposite-Large-Preorder l1)
    (Y : type-opposite-Large-Preorder l2) → Prop (β l2 l1)
  leq-prop-opposite-Large-Preorder X Y = leq-prop-Large-Preorder P Y X

  leq-opposite-Large-Preorder :
    {l1 l2 : Level}
    (X : type-opposite-Large-Preorder l1)
    (Y : type-opposite-Large-Preorder l2) → UU (β l2 l1)
  leq-opposite-Large-Preorder X Y =
    type-Prop (leq-prop-opposite-Large-Preorder X Y)

  transitive-leq-opposite-Large-Preorder :
    {l1 l2 l3 : Level}
    (X : type-opposite-Large-Preorder l1)
    (Y : type-opposite-Large-Preorder l2)
    (Z : type-opposite-Large-Preorder l3) →
    leq-opposite-Large-Preorder Y Z →
    leq-opposite-Large-Preorder X Y →
    leq-opposite-Large-Preorder X Z
  transitive-leq-opposite-Large-Preorder X Y Z g f =
    transitive-leq-Large-Preorder P Z Y X f g

  refl-leq-opposite-Large-Preorder :
    {l1 : Level} (X : type-opposite-Large-Preorder l1) →
    leq-opposite-Large-Preorder X X
  refl-leq-opposite-Large-Preorder = refl-leq-Large-Preorder P

  opposite-Large-Preorder : Large-Preorder α (λ l1 l2 → β l2 l1)
  opposite-Large-Preorder =
    make-Large-Preorder
      type-opposite-Large-Preorder
      leq-prop-opposite-Large-Preorder
      refl-leq-opposite-Large-Preorder
      transitive-leq-opposite-Large-Preorder
```

## Properties

### The opposite large preorder construction is a strict involution

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (P : Large-Preorder α β)
  where

  is-involution-opposite-Large-Preorder :
    opposite-Large-Preorder (opposite-Large-Preorder P) ＝ω P
  is-involution-opposite-Large-Preorder = reflω
```
