# Associative algebras over commutative rings

```agda
module commutative-algebra.associative-algebras-commutative-rings where
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
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.semigroups
```

</details>

## Idea

An [algebra](commutative-algebra.algebras-commutative-rings.md) over a
[commutative ring](commutative-algebra.commutative-rings.md) is
{{#concept "associative" Disambiguation="algebra over a commutative ring" WDID=Q744960 WD="associative algebra" Agda=associative-algebra-Commutative-Ring}}
if its multiplication operation is associative.

## Definition

```agda
module _
  {l1 l2 : Level}
  (R : Commutative-Ring l1)
  (A : algebra-Commutative-Ring l2 R)
  where

  is-associative-prop-algebra-Commutative-Ring : Prop l2
  is-associative-prop-algebra-Commutative-Ring =
    Π-Prop
      ( type-algebra-Commutative-Ring R A)
      ( λ x →
        Π-Prop
          ( type-algebra-Commutative-Ring R A)
          ( λ y →
            Π-Prop
              ( type-algebra-Commutative-Ring R A)
              ( λ z →
                Id-Prop
                  ( set-algebra-Commutative-Ring R A)
                  ( mul-algebra-Commutative-Ring R A
                    ( mul-algebra-Commutative-Ring R A x y)
                    ( z))
                  ( mul-algebra-Commutative-Ring R A
                    ( x)
                    ( mul-algebra-Commutative-Ring R A y z)))))

  is-associative-algebra-Commutative-Ring : UU l2
  is-associative-algebra-Commutative-Ring =
    type-Prop is-associative-prop-algebra-Commutative-Ring

associative-algebra-Commutative-Ring :
  {l1 : Level} (l2 : Level) → Commutative-Ring l1 → UU (l1 ⊔ lsuc l2)
associative-algebra-Commutative-Ring l2 R =
  type-subtype
    ( is-associative-prop-algebra-Commutative-Ring {l2 = l2} R)

module _
  {l1 l2 : Level}
  (R : Commutative-Ring l1)
  (A : associative-algebra-Commutative-Ring l2 R)
  where

  algebra-associative-algebra-Commutative-Ring : algebra-Commutative-Ring l2 R
  algebra-associative-algebra-Commutative-Ring = pr1 A

  ab-add-associative-algebra-Commutative-Ring : Ab l2
  ab-add-associative-algebra-Commutative-Ring =
    ab-add-algebra-Commutative-Ring
      ( R)
      ( algebra-associative-algebra-Commutative-Ring)

  set-associative-algebra-Commutative-Ring : Set l2
  set-associative-algebra-Commutative-Ring =
    set-Ab ab-add-associative-algebra-Commutative-Ring

  type-associative-algebra-Commutative-Ring : UU l2
  type-associative-algebra-Commutative-Ring =
    type-Ab ab-add-associative-algebra-Commutative-Ring

  mul-associative-algebra-Commutative-Ring :
    type-associative-algebra-Commutative-Ring →
    type-associative-algebra-Commutative-Ring →
    type-associative-algebra-Commutative-Ring
  mul-associative-algebra-Commutative-Ring =
    mul-algebra-Commutative-Ring
      ( R)
      ( algebra-associative-algebra-Commutative-Ring)

  associative-mul-associative-algebra-Commutative-Ring :
    (x y z : type-associative-algebra-Commutative-Ring) →
    mul-associative-algebra-Commutative-Ring
      ( mul-associative-algebra-Commutative-Ring x y)
      ( z) ＝
    mul-associative-algebra-Commutative-Ring
      ( x)
      ( mul-associative-algebra-Commutative-Ring y z)
  associative-mul-associative-algebra-Commutative-Ring = pr2 A

  semigroup-mul-associative-algebra-Commutative-Ring : Semigroup l2
  semigroup-mul-associative-algebra-Commutative-Ring =
    ( set-associative-algebra-Commutative-Ring ,
      mul-associative-algebra-Commutative-Ring ,
      associative-mul-associative-algebra-Commutative-Ring)
```

## Properties

### Every commutative ring is an associative algebra over itself

```agda
associative-algebra-commutative-ring-Commutative-Ring :
  {l : Level} (R : Commutative-Ring l) →
  associative-algebra-Commutative-Ring l R
associative-algebra-commutative-ring-Commutative-Ring R =
  ( algebra-commutative-ring-Commutative-Ring R ,
    associative-mul-Commutative-Ring R)
```

## External links

- [Associative algebra](https://en.wikipedia.org/wiki/Associative_algebra) on
  Wikipedia
