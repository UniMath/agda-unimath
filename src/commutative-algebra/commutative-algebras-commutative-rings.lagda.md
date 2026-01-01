# Commutative algebras over commutative rings

```agda
module commutative-algebra.commutative-algebras-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.unital-associative-algebras-commutative-rings

open import commutative-algebra.algebras-commutative-rings
open import foundation.propositions
open import ring-theory.rings
open import foundation.identity-types
open import foundation.sets
open import group-theory.abelian-groups
open import foundation.dependent-pair-types
open import foundation.subtypes
open import foundation.universe-levels
open import commutative-algebra.algebras-commutative-rings
open import commutative-algebra.commutative-rings
open import commutative-algebra.unital-associative-algebras-commutative-rings

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.abelian-groups

open import ring-theory.rings
```

</details>

## Idea

A
{{#concept "commutative algebra" Disambiguation="over a commutative ring" Agda=commutative-algebra-Commutative-Ring}}
over a [commutative ring](commutative-algebra.commutative-rings.md) is a
[unital associative algebra](commutative-algebra.unital-associative-algebras-commutative-rings.md)
whose multiplication operation is commutative.

## Definition

```agda
module _
  {l1 l2 : Level}
  (R : Commutative-Ring l1)
  (A : unital-associative-algebra-Commutative-Ring l2 R)
  where

  is-commutative-prop-unital-associative-algebra-Commutative-Ring : Prop l2
  is-commutative-prop-unital-associative-algebra-Commutative-Ring =
    Π-Prop
      ( type-unital-associative-algebra-Commutative-Ring R A)
      ( λ x →
        Π-Prop
          ( type-unital-associative-algebra-Commutative-Ring R A)
          ( λ y →
            Id-Prop
              ( set-unital-associative-algebra-Commutative-Ring R A)
              ( mul-unital-associative-algebra-Commutative-Ring R A x y)
              ( mul-unital-associative-algebra-Commutative-Ring R A y x)))

  is-commutative-unital-associative-algebra-Commutative-Ring : UU l2
  is-commutative-unital-associative-algebra-Commutative-Ring =
    type-Prop is-commutative-prop-unital-associative-algebra-Commutative-Ring

commutative-algebra-Commutative-Ring :
  {l1 : Level} (l2 : Level) → Commutative-Ring l1 → UU (l1 ⊔ lsuc l2)
commutative-algebra-Commutative-Ring l2 R =
  type-subtype
    ( is-commutative-prop-unital-associative-algebra-Commutative-Ring
      { l2 = l2}
      ( R))
```

## Properties

```agda
module _
  {l1 l2 : Level}
  (R : Commutative-Ring l1)
  (A : commutative-algebra-Commutative-Ring l2 R)
  where

  unital-associative-algebra-commutative-algebra-Commutative-Ring :
    unital-associative-algebra-Commutative-Ring l2 R
  unital-associative-algebra-commutative-algebra-Commutative-Ring = pr1 A

  algebra-commutative-algebra-Commutative-Ring : algebra-Commutative-Ring l2 R
  algebra-commutative-algebra-Commutative-Ring =
    algebra-unital-associative-algebra-Commutative-Ring
      ( R)
      ( unital-associative-algebra-commutative-algebra-Commutative-Ring)

  ab-add-commutative-algebra-Commutative-Ring : Ab l2
  ab-add-commutative-algebra-Commutative-Ring =
    ab-add-algebra-Commutative-Ring
      ( R)
      ( algebra-commutative-algebra-Commutative-Ring)

  set-commutative-algebra-Commutative-Ring : Set l2
  set-commutative-algebra-Commutative-Ring =
    set-Ab ab-add-commutative-algebra-Commutative-Ring

  type-commutative-algebra-Commutative-Ring : UU l2
  type-commutative-algebra-Commutative-Ring =
    type-Ab ab-add-commutative-algebra-Commutative-Ring

  ring-commutative-algebra-Commutative-Ring : Ring l2
  ring-commutative-algebra-Commutative-Ring =
    ring-unital-associative-algebra-Commutative-Ring
      ( R)
      ( unital-associative-algebra-commutative-algebra-Commutative-Ring)

  mul-commutative-algebra-Commutative-Ring :
    type-commutative-algebra-Commutative-Ring →
    type-commutative-algebra-Commutative-Ring →
    type-commutative-algebra-Commutative-Ring
  mul-commutative-algebra-Commutative-Ring =
    mul-algebra-Commutative-Ring
      ( R)
      ( algebra-commutative-algebra-Commutative-Ring)

  commutative-mul-commutative-algebra-Commutative-Ring :
    (x y : type-commutative-algebra-Commutative-Ring) →
    mul-commutative-algebra-Commutative-Ring x y ＝
    mul-commutative-algebra-Commutative-Ring y x
  commutative-mul-commutative-algebra-Commutative-Ring = pr2 A
```

### A commutative algebra over a commutative ring is itself a commutative ring

```agda
module _
  {l1 l2 : Level}
  (R : Commutative-Ring l1)
  (A : commutative-algebra-Commutative-Ring l2 R)
  where

  commutative-ring-commutative-algebra-Commutative-Ring : Commutative-Ring l2
  commutative-ring-commutative-algebra-Commutative-Ring =
    ( ring-commutative-algebra-Commutative-Ring R A ,
      commutative-mul-commutative-algebra-Commutative-Ring R A)
```

## External links

- [Commutative algebra](https://ncatlab.org/nlab/show/commutative+algebra) on
  $n$Lab
