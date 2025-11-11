# Vector spaces

```agda
module linear-algebra.vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.sets
open import foundation.universe-levels
open import group-theory.abelian-groups
open import commutative-algebra.local-commutative-rings
open import linear-algebra.left-modules-commutative-rings
```

</details>

## Idea

A {{#concept "vector space" WD="vector space" WDID=Q125977}} is a
[left module](linear-algebra.left-modules-rings.md) over a
[local commutative ring](commutative-algebra.local-commutative-rings.md).

## Definition

```agda
Vector-Space :
  {l1 : Level} (l2 : Level) → Local-Commutative-Ring l1 → UU (l1 ⊔ lsuc l2)
Vector-Space l2 R =
  left-module-Commutative-Ring l2 (commutative-ring-Local-Commutative-Ring R)
```

## Properties

```agda
module _
  {l1 l2 : Level} (R : Local-Commutative-Ring l1) (V : Vector-Space l2 R)
  where

  ab-Vector-Space : Ab l2
  ab-Vector-Space =
    ab-left-module-Commutative-Ring
      ( commutative-ring-Local-Commutative-Ring R)
      ( V)

  set-Vector-Space : Set l2
  set-Vector-Space = set-Ab ab-Vector-Space

  type-Vector-Space : UU l2
  type-Vector-Space = type-Ab ab-Vector-Space

  add-Vector-Space : type-Vector-Space → type-Vector-Space → type-Vector-Space
  add-Vector-Space = add-Ab ab-Vector-Space
```
