# Opposite preorders

```agda
module order-theory.opposite-preorders where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import order-theory.preorders
```

</details>

## Idea

Let `X` be a [preorder](order-theory.preorders.md), its
{{#concept "opposite" Disambiguation="preorder" Agda=opposite-Preorder}} `Xᵒᵖ`
is given by reversing the relation.

## Definition

### The opposite preorder

```agda
module _
  {l1 l2 : Level} (P : Preorder l1 l2)
  where

  type-opposite-Preorder : UU l1
  type-opposite-Preorder = type-Preorder P

  leq-prop-opposite-Preorder :
    (X Y : type-opposite-Preorder) → Prop l2
  leq-prop-opposite-Preorder X Y = leq-prop-Preorder P Y X

  leq-opposite-Preorder :
    (X Y : type-opposite-Preorder) → UU l2
  leq-opposite-Preorder X Y =
    type-Prop (leq-prop-opposite-Preorder X Y)

  transitive-leq-opposite-Preorder :
    (X Y Z : type-opposite-Preorder) →
    leq-opposite-Preorder Y Z →
    leq-opposite-Preorder X Y →
    leq-opposite-Preorder X Z
  transitive-leq-opposite-Preorder X Y Z g f =
    transitive-leq-Preorder P Z Y X f g

  refl-leq-opposite-Preorder :
    (X : type-opposite-Preorder) → leq-opposite-Preorder X X
  refl-leq-opposite-Preorder = refl-leq-Preorder P

  opposite-Preorder : Preorder l1 l2
  opposite-Preorder =
    ( type-opposite-Preorder ,
      leq-prop-opposite-Preorder ,
      refl-leq-opposite-Preorder ,
      transitive-leq-opposite-Preorder)
```

## Properties

### The opposite preorder construction is a strict involution

```agda
module _
  {l1 l2 : Level} (P : Preorder l1 l2)
  where

  is-involution-opposite-Preorder : opposite-Preorder (opposite-Preorder P) ＝ P
  is-involution-opposite-Preorder = refl
```
