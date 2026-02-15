# Unital algebras over commutative rings

```agda
module commutative-algebra.unital-algebras-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.algebras-commutative-rings
open import commutative-algebra.commutative-rings

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.unital-binary-operations
open import foundation.universe-levels

open import group-theory.abelian-groups
```

</details>

## Idea

An [algebra](commutative-algebra.algebras-commutative-rings.md) over a
[commutative ring](commutative-algebra.commutative-rings.md) is
{{#concept "unital" WDID=Q2621172 WD="unital algebra" Disambiguation="algebra over a commutative ring"}}
if its multiplication operation is
[unital](foundation.unital-binary-operations.md).

## Definition

```agda
module _
  {l1 l2 : Level}
  (R : Commutative-Ring l1)
  (A : algebra-Commutative-Ring l2 R)
  where

  is-unital-prop-algebra-Commutative-Ring : Prop l2
  is-unital-prop-algebra-Commutative-Ring =
    is-unital-prop-Set
      ( set-algebra-Commutative-Ring R A)
      ( mul-algebra-Commutative-Ring R A)

  is-unital-algebra-Commutative-Ring : UU l2
  is-unital-algebra-Commutative-Ring =
    type-Prop is-unital-prop-algebra-Commutative-Ring

unital-algebra-Commutative-Ring :
  {l1 : Level} (l2 : Level) → Commutative-Ring l1 → UU (l1 ⊔ lsuc l2)
unital-algebra-Commutative-Ring l2 R =
  type-subtype (is-unital-prop-algebra-Commutative-Ring {l2 = l2} R)
```

## Properties

```agda
module _
  {l1 l2 : Level}
  (R : Commutative-Ring l1)
  (A : unital-algebra-Commutative-Ring l2 R)
  where

  algebra-unital-algebra-Commutative-Ring : algebra-Commutative-Ring l2 R
  algebra-unital-algebra-Commutative-Ring = pr1 A

  set-unital-algebra-Commutative-Ring : Set l2
  set-unital-algebra-Commutative-Ring =
    set-algebra-Commutative-Ring R algebra-unital-algebra-Commutative-Ring

  type-unital-algebra-Commutative-Ring : UU l2
  type-unital-algebra-Commutative-Ring =
    type-Set set-unital-algebra-Commutative-Ring

  ab-add-unital-algebra-Commutative-Ring : Ab l2
  ab-add-unital-algebra-Commutative-Ring =
    ab-add-algebra-Commutative-Ring R algebra-unital-algebra-Commutative-Ring

  add-unital-algebra-Commutative-Ring :
    type-unital-algebra-Commutative-Ring →
    type-unital-algebra-Commutative-Ring →
    type-unital-algebra-Commutative-Ring
  add-unital-algebra-Commutative-Ring =
    add-Ab ab-add-unital-algebra-Commutative-Ring

  zero-unital-algebra-Commutative-Ring : type-unital-algebra-Commutative-Ring
  zero-unital-algebra-Commutative-Ring =
    zero-Ab ab-add-unital-algebra-Commutative-Ring

  neg-unital-algebra-Commutative-Ring :
    type-unital-algebra-Commutative-Ring → type-unital-algebra-Commutative-Ring
  neg-unital-algebra-Commutative-Ring =
    neg-Ab ab-add-unital-algebra-Commutative-Ring

  scalar-mul-unital-algebra-Commutative-Ring :
    type-Commutative-Ring R →
    type-unital-algebra-Commutative-Ring →
    type-unital-algebra-Commutative-Ring
  scalar-mul-unital-algebra-Commutative-Ring =
    scalar-mul-algebra-Commutative-Ring
      ( R)
      ( algebra-unital-algebra-Commutative-Ring)

  mul-unital-algebra-Commutative-Ring :
    type-unital-algebra-Commutative-Ring →
    type-unital-algebra-Commutative-Ring →
    type-unital-algebra-Commutative-Ring
  mul-unital-algebra-Commutative-Ring =
    mul-algebra-Commutative-Ring R algebra-unital-algebra-Commutative-Ring

  is-unital-mul-unital-algebra-Commutative-Ring :
    is-unital mul-unital-algebra-Commutative-Ring
  is-unital-mul-unital-algebra-Commutative-Ring = pr2 A

  one-unital-algebra-Commutative-Ring : type-unital-algebra-Commutative-Ring
  one-unital-algebra-Commutative-Ring =
    pr1 is-unital-mul-unital-algebra-Commutative-Ring

  left-unit-law-mul-unital-algebra-Commutative-Ring :
    (x : type-unital-algebra-Commutative-Ring) →
    mul-unital-algebra-Commutative-Ring one-unital-algebra-Commutative-Ring x ＝
    x
  left-unit-law-mul-unital-algebra-Commutative-Ring =
    pr1 (pr2 is-unital-mul-unital-algebra-Commutative-Ring)

  right-unit-law-mul-unital-algebra-Commutative-Ring :
    (x : type-unital-algebra-Commutative-Ring) →
    mul-unital-algebra-Commutative-Ring x one-unital-algebra-Commutative-Ring ＝
    x
  right-unit-law-mul-unital-algebra-Commutative-Ring =
    pr2 (pr2 is-unital-mul-unital-algebra-Commutative-Ring)
```

### Every commutative ring is a unital algebra over itself

```agda
unital-algebra-commutative-ring-Commutative-Ring :
  {l : Level} (R : Commutative-Ring l) → unital-algebra-Commutative-Ring l R
unital-algebra-commutative-ring-Commutative-Ring R =
  ( algebra-commutative-ring-Commutative-Ring R ,
    is-unital-Commutative-Ring R)
```
