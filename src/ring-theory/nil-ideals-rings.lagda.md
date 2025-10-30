# Nil ideals of rings

```agda
module ring-theory.nil-ideals-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositions
open import foundation.universe-levels

open import ring-theory.ideals-rings
open import ring-theory.left-ideals-rings
open import ring-theory.nilpotent-elements-rings
open import ring-theory.right-ideals-rings
open import ring-theory.rings
```

</details>

## Idea

A {{#concept "nil ideal" Disambiguation="in a ring" Agda=is-nil-ideal-Ring}} in
a [ring](ring-theory.rings.md) is an [ideal](ring-theory.ideals-rings.md) in
which every element is [nilpotent](ring-theory.nilpotent-elements-rings.md).

## Definition

### Nil left ideals

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (I : left-ideal-Ring l2 R)
  where

  is-nil-left-ideal-ring-Prop : Prop (l1 ⊔ l2)
  is-nil-left-ideal-ring-Prop =
    Π-Prop
      ( type-left-ideal-Ring R I)
      ( λ x →
        is-nilpotent-element-ring-Prop R (inclusion-left-ideal-Ring R I x))

  is-nil-left-ideal-Ring : UU (l1 ⊔ l2)
  is-nil-left-ideal-Ring = type-Prop is-nil-left-ideal-ring-Prop

  is-prop-is-nil-left-ideal-Ring : is-prop is-nil-left-ideal-Ring
  is-prop-is-nil-left-ideal-Ring =
    is-prop-type-Prop is-nil-left-ideal-ring-Prop
```

### Nil right ideals

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (I : right-ideal-Ring l2 R)
  where

  is-nil-right-ideal-ring-Prop : Prop (l1 ⊔ l2)
  is-nil-right-ideal-ring-Prop =
    Π-Prop
      ( type-right-ideal-Ring R I)
      ( λ x →
        is-nilpotent-element-ring-Prop R (inclusion-right-ideal-Ring R I x))

  is-nil-right-ideal-Ring : UU (l1 ⊔ l2)
  is-nil-right-ideal-Ring = type-Prop is-nil-right-ideal-ring-Prop

  is-prop-is-nil-right-ideal-Ring : is-prop is-nil-right-ideal-Ring
  is-prop-is-nil-right-ideal-Ring =
    is-prop-type-Prop is-nil-right-ideal-ring-Prop
```

### Nil ideals

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (I : ideal-Ring l2 R)
  where

  is-nil-ideal-ring-Prop : Prop (l1 ⊔ l2)
  is-nil-ideal-ring-Prop =
    Π-Prop
      ( type-ideal-Ring R I)
      ( λ x →
        is-nilpotent-element-ring-Prop R (inclusion-ideal-Ring R I x))

  is-nil-ideal-Ring : UU (l1 ⊔ l2)
  is-nil-ideal-Ring = type-Prop is-nil-ideal-ring-Prop

  is-prop-is-nil-ideal-Ring : is-prop is-nil-ideal-Ring
  is-prop-is-nil-ideal-Ring =
    is-prop-type-Prop is-nil-ideal-ring-Prop
```
