# Unital associative algebras over commutative rings

```agda
module commutative-algebra.unital-associative-algebras-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.algebras-commutative-rings
open import commutative-algebra.associative-algebras-commutative-rings
open import commutative-algebra.commutative-rings
open import commutative-algebra.homomorphisms-commutative-rings
open import commutative-algebra.unital-algebras-commutative-rings

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.unital-binary-operations
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.central-elements-monoids
open import group-theory.monoids
open import group-theory.semigroups

open import ring-theory.central-elements-rings
open import ring-theory.homomorphisms-rings
open import ring-theory.rings
```

</details>

## Idea

An [algebra](commutative-algebra.algebras-commutative-rings.md) over a
[commutative ring](commutative-algebra.commutative-rings.md) that is both
[unital](commutative-algebra.unital-algebras-commutative-rings.md) and
[associative](commutative-algebra.associative-algebras-commutative-rings.md) is
itself a [ring](ring-theory.rings.md).

## Definition

```agda
module _
  {l1 l2 : Level}
  (R : Commutative-Ring l1)
  (A : associative-algebra-Commutative-Ring l2 R)
  where

  is-unital-prop-associative-algebra-Commutative-Ring : Prop l2
  is-unital-prop-associative-algebra-Commutative-Ring =
    is-unital-prop-Set
      ( set-associative-algebra-Commutative-Ring R A)
      ( mul-associative-algebra-Commutative-Ring R A)

  is-unital-associative-algebra-Commutative-Ring : UU l2
  is-unital-associative-algebra-Commutative-Ring =
    type-Prop is-unital-prop-associative-algebra-Commutative-Ring

unital-associative-algebra-Commutative-Ring :
  {l1 : Level} (l2 : Level) (R : Commutative-Ring l1) → UU (l1 ⊔ lsuc l2)
unital-associative-algebra-Commutative-Ring l2 R =
  type-subtype (is-unital-prop-associative-algebra-Commutative-Ring {l2 = l2} R)
```

## Properties

```agda
module _
  {l1 l2 : Level}
  (R : Commutative-Ring l1)
  (A : unital-associative-algebra-Commutative-Ring l2 R)
  where

  associative-algebra-unital-associative-algebra-Commutative-Ring :
    associative-algebra-Commutative-Ring l2 R
  associative-algebra-unital-associative-algebra-Commutative-Ring = pr1 A

  algebra-unital-associative-algebra-Commutative-Ring :
    algebra-Commutative-Ring l2 R
  algebra-unital-associative-algebra-Commutative-Ring =
    algebra-associative-algebra-Commutative-Ring
      ( R)
      ( associative-algebra-unital-associative-algebra-Commutative-Ring)

  ab-add-unital-associative-algebra-Commutative-Ring : Ab l2
  ab-add-unital-associative-algebra-Commutative-Ring =
    ab-add-algebra-Commutative-Ring
      ( R)
      ( algebra-unital-associative-algebra-Commutative-Ring)

  set-unital-associative-algebra-Commutative-Ring : Set l2
  set-unital-associative-algebra-Commutative-Ring =
    set-Ab ab-add-unital-associative-algebra-Commutative-Ring

  type-unital-associative-algebra-Commutative-Ring : UU l2
  type-unital-associative-algebra-Commutative-Ring =
    type-Ab ab-add-unital-associative-algebra-Commutative-Ring

  add-unital-associative-algebra-Commutative-Ring :
    type-unital-associative-algebra-Commutative-Ring →
    type-unital-associative-algebra-Commutative-Ring →
    type-unital-associative-algebra-Commutative-Ring
  add-unital-associative-algebra-Commutative-Ring =
    add-Ab ab-add-unital-associative-algebra-Commutative-Ring

  mul-unital-associative-algebra-Commutative-Ring :
    type-unital-associative-algebra-Commutative-Ring →
    type-unital-associative-algebra-Commutative-Ring →
    type-unital-associative-algebra-Commutative-Ring
  mul-unital-associative-algebra-Commutative-Ring =
    mul-algebra-Commutative-Ring
      ( R)
      ( algebra-unital-associative-algebra-Commutative-Ring)

  associative-mul-unital-associative-algebra-Commutative-Ring :
    (x y z : type-unital-associative-algebra-Commutative-Ring) →
    mul-unital-associative-algebra-Commutative-Ring
      ( mul-unital-associative-algebra-Commutative-Ring x y)
      ( z) ＝
    mul-unital-associative-algebra-Commutative-Ring
      ( x)
      ( mul-unital-associative-algebra-Commutative-Ring y z)
  associative-mul-unital-associative-algebra-Commutative-Ring =
    associative-mul-associative-algebra-Commutative-Ring
      ( R)
      ( associative-algebra-unital-associative-algebra-Commutative-Ring)

  is-unital-mul-unital-associative-algebra-Commutative-Ring :
    is-unital mul-unital-associative-algebra-Commutative-Ring
  is-unital-mul-unital-associative-algebra-Commutative-Ring = pr2 A

  unital-algebra-unital-associative-algebra-Commutative-Ring :
    unital-algebra-Commutative-Ring l2 R
  unital-algebra-unital-associative-algebra-Commutative-Ring =
    ( algebra-unital-associative-algebra-Commutative-Ring ,
      is-unital-mul-unital-associative-algebra-Commutative-Ring)

  semigroup-mul-unital-associative-algebra-Commutative-Ring : Semigroup l2
  semigroup-mul-unital-associative-algebra-Commutative-Ring =
    semigroup-mul-associative-algebra-Commutative-Ring
      ( R)
      ( associative-algebra-unital-associative-algebra-Commutative-Ring)

  monoid-mul-unital-associative-algebra-Commutative-Ring : Monoid l2
  monoid-mul-unital-associative-algebra-Commutative-Ring =
    ( semigroup-mul-unital-associative-algebra-Commutative-Ring ,
      is-unital-mul-unital-associative-algebra-Commutative-Ring)

  one-unital-associative-algebra-Commutative-Ring :
    type-unital-associative-algebra-Commutative-Ring
  one-unital-associative-algebra-Commutative-Ring =
    unit-Monoid monoid-mul-unital-associative-algebra-Commutative-Ring

  scalar-mul-unital-associative-algebra-Commutative-Ring :
    type-Commutative-Ring R → type-unital-associative-algebra-Commutative-Ring →
    type-unital-associative-algebra-Commutative-Ring
  scalar-mul-unital-associative-algebra-Commutative-Ring =
    scalar-mul-algebra-Commutative-Ring
      ( R)
      ( algebra-unital-associative-algebra-Commutative-Ring)

  left-distributive-mul-add-unital-associative-algebra-Commutative-Ring :
    (x y z : type-unital-associative-algebra-Commutative-Ring) →
    mul-unital-associative-algebra-Commutative-Ring
      ( x)
      ( add-unital-associative-algebra-Commutative-Ring y z) ＝
    add-unital-associative-algebra-Commutative-Ring
      ( mul-unital-associative-algebra-Commutative-Ring x y)
      ( mul-unital-associative-algebra-Commutative-Ring x z)
  left-distributive-mul-add-unital-associative-algebra-Commutative-Ring =
    left-distributive-mul-add-algebra-Commutative-Ring
      ( R)
      ( algebra-unital-associative-algebra-Commutative-Ring)

  right-distributive-mul-add-unital-associative-algebra-Commutative-Ring :
    (x y z : type-unital-associative-algebra-Commutative-Ring) →
    mul-unital-associative-algebra-Commutative-Ring
      ( add-unital-associative-algebra-Commutative-Ring x y)
      ( z) ＝
    add-unital-associative-algebra-Commutative-Ring
      ( mul-unital-associative-algebra-Commutative-Ring x z)
      ( mul-unital-associative-algebra-Commutative-Ring y z)
  right-distributive-mul-add-unital-associative-algebra-Commutative-Ring =
    right-distributive-mul-add-algebra-Commutative-Ring
      ( R)
      ( algebra-unital-associative-algebra-Commutative-Ring)

  left-unit-law-mul-unital-associative-algebra-Commutative-Ring :
    (x : type-unital-associative-algebra-Commutative-Ring) →
    mul-unital-associative-algebra-Commutative-Ring
      ( one-unital-associative-algebra-Commutative-Ring)
      ( x) ＝
    x
  left-unit-law-mul-unital-associative-algebra-Commutative-Ring =
    left-unit-law-mul-Monoid
      ( monoid-mul-unital-associative-algebra-Commutative-Ring)

  left-unit-law-scalar-mul-unital-associative-algebra-Commutative-Ring :
    (x : type-unital-associative-algebra-Commutative-Ring) →
    scalar-mul-unital-associative-algebra-Commutative-Ring
      ( one-Commutative-Ring R)
      ( x) ＝
    x
  left-unit-law-scalar-mul-unital-associative-algebra-Commutative-Ring =
    left-unit-law-scalar-mul-algebra-Commutative-Ring
      ( R)
      ( algebra-unital-associative-algebra-Commutative-Ring)

  right-distributive-scalar-mul-add-unital-associative-algebra-Commutative-Ring :
    (r s : type-Commutative-Ring R) →
    (x : type-unital-associative-algebra-Commutative-Ring) →
    scalar-mul-unital-associative-algebra-Commutative-Ring
      ( add-Commutative-Ring R r s)
      ( x) ＝
    add-unital-associative-algebra-Commutative-Ring
      ( scalar-mul-unital-associative-algebra-Commutative-Ring r x)
      ( scalar-mul-unital-associative-algebra-Commutative-Ring s x)
  right-distributive-scalar-mul-add-unital-associative-algebra-Commutative-Ring =
    right-distributive-scalar-mul-add-algebra-Commutative-Ring
      ( R)
      ( algebra-unital-associative-algebra-Commutative-Ring)

  associative-scalar-mul-unital-associative-algebra-Commutative-Ring :
    (r s : type-Commutative-Ring R) →
    (x : type-unital-associative-algebra-Commutative-Ring) →
    scalar-mul-unital-associative-algebra-Commutative-Ring
      ( mul-Commutative-Ring R r s)
      ( x) ＝
    scalar-mul-unital-associative-algebra-Commutative-Ring
      ( r)
      ( scalar-mul-unital-associative-algebra-Commutative-Ring s x)
  associative-scalar-mul-unital-associative-algebra-Commutative-Ring =
    associative-scalar-mul-algebra-Commutative-Ring
      ( R)
      ( algebra-unital-associative-algebra-Commutative-Ring)

  associative-scalar-mul-mul-unital-associative-algebra-Commutative-Ring :
    (r : type-Commutative-Ring R) →
    (x y : type-unital-associative-algebra-Commutative-Ring) →
    mul-unital-associative-algebra-Commutative-Ring
      ( scalar-mul-unital-associative-algebra-Commutative-Ring r x)
      ( y) ＝
    scalar-mul-unital-associative-algebra-Commutative-Ring
      ( r)
      ( mul-unital-associative-algebra-Commutative-Ring x y)
  associative-scalar-mul-mul-unital-associative-algebra-Commutative-Ring =
    associative-scalar-mul-mul-algebra-Commutative-Ring
      ( R)
      ( algebra-unital-associative-algebra-Commutative-Ring)

  left-swap-scalar-mul-mul-unital-associative-algebra-Commutative-Ring :
    (r : type-Commutative-Ring R) →
    (x y : type-unital-associative-algebra-Commutative-Ring) →
    scalar-mul-unital-associative-algebra-Commutative-Ring
      ( r)
      ( mul-unital-associative-algebra-Commutative-Ring x y) ＝
    mul-unital-associative-algebra-Commutative-Ring
      ( x)
      ( scalar-mul-unital-associative-algebra-Commutative-Ring r y)
  left-swap-scalar-mul-mul-unital-associative-algebra-Commutative-Ring =
    left-swap-scalar-mul-mul-algebra-Commutative-Ring
      ( R)
      ( algebra-unital-associative-algebra-Commutative-Ring)
```

### A unital associative algebra is a ring

```agda
module _
  {l1 l2 : Level}
  (R : Commutative-Ring l1)
  (A : unital-associative-algebra-Commutative-Ring l2 R)
  where

  ring-unital-associative-algebra-Commutative-Ring : Ring l2
  ring-unital-associative-algebra-Commutative-Ring =
    ( ab-add-unital-associative-algebra-Commutative-Ring R A ,
      ( mul-unital-associative-algebra-Commutative-Ring R A ,
        associative-mul-unital-associative-algebra-Commutative-Ring R A) ,
      is-unital-mul-unital-associative-algebra-Commutative-Ring R A ,
      left-distributive-mul-add-unital-associative-algebra-Commutative-Ring
        ( R)
        ( A) ,
      right-distributive-mul-add-unital-associative-algebra-Commutative-Ring
        ( R)
        ( A))
```

### Given a unital associative algebra `A` over `R`, there is a ring homomorphism from `R` to `A`

```agda
module _
  {l1 l2 : Level}
  (R : Commutative-Ring l1)
  (A : unital-associative-algebra-Commutative-Ring l2 R)
  where

  map-hom-ring-unital-associative-algebra-Commutative-Ring :
    type-Commutative-Ring R →
    type-unital-associative-algebra-Commutative-Ring R A
  map-hom-ring-unital-associative-algebra-Commutative-Ring r =
    scalar-mul-unital-associative-algebra-Commutative-Ring R A
      ( r)
      ( one-unital-associative-algebra-Commutative-Ring R A)

  abstract
    preserves-one-hom-ring-unital-associative-algebra-Commutative-Ring :
      map-hom-ring-unital-associative-algebra-Commutative-Ring
        ( one-Commutative-Ring R) ＝
      one-unital-associative-algebra-Commutative-Ring R A
    preserves-one-hom-ring-unital-associative-algebra-Commutative-Ring =
      left-unit-law-scalar-mul-unital-associative-algebra-Commutative-Ring
        ( R)
        ( A)
        ( one-unital-associative-algebra-Commutative-Ring R A)

    preserves-add-hom-ring-unital-associative-algebra-Commutative-Ring :
      (r s : type-Commutative-Ring R) →
      map-hom-ring-unital-associative-algebra-Commutative-Ring
        ( add-Commutative-Ring R r s) ＝
      add-unital-associative-algebra-Commutative-Ring R A
        ( map-hom-ring-unital-associative-algebra-Commutative-Ring r)
        ( map-hom-ring-unital-associative-algebra-Commutative-Ring s)
    preserves-add-hom-ring-unital-associative-algebra-Commutative-Ring r s =
      right-distributive-scalar-mul-add-unital-associative-algebra-Commutative-Ring
        ( R)
        ( A)
        ( r)
        ( s)
        ( one-unital-associative-algebra-Commutative-Ring R A)

    preserves-mul-hom-ring-unital-associative-algebra-Commutative-Ring :
      (r s : type-Commutative-Ring R) →
      map-hom-ring-unital-associative-algebra-Commutative-Ring
        ( mul-Commutative-Ring R r s) ＝
      mul-unital-associative-algebra-Commutative-Ring R A
        ( map-hom-ring-unital-associative-algebra-Commutative-Ring r)
        ( map-hom-ring-unital-associative-algebra-Commutative-Ring s)
    preserves-mul-hom-ring-unital-associative-algebra-Commutative-Ring r s =
      inv
        ( equational-reasoning
          mul-unital-associative-algebra-Commutative-Ring R A
            ( map-hom-ring-unital-associative-algebra-Commutative-Ring r)
            ( map-hom-ring-unital-associative-algebra-Commutative-Ring s)
          ＝
            scalar-mul-unital-associative-algebra-Commutative-Ring R A
              ( r)
              ( mul-unital-associative-algebra-Commutative-Ring R A
                ( one-unital-associative-algebra-Commutative-Ring R A)
                ( map-hom-ring-unital-associative-algebra-Commutative-Ring s))
            by
              associative-scalar-mul-mul-unital-associative-algebra-Commutative-Ring
                ( R)
                ( A)
                ( _)
                ( _)
                ( _)
          ＝
            scalar-mul-unital-associative-algebra-Commutative-Ring R A
              ( r)
              ( map-hom-ring-unital-associative-algebra-Commutative-Ring s)
            by
              ap
                ( scalar-mul-unital-associative-algebra-Commutative-Ring R A r)
                ( left-unit-law-mul-unital-associative-algebra-Commutative-Ring
                  ( R)
                  ( A)
                  ( _))
          ＝
            map-hom-ring-unital-associative-algebra-Commutative-Ring
              ( mul-Commutative-Ring R r s)
            by
              inv
                ( associative-scalar-mul-unital-associative-algebra-Commutative-Ring
                  ( R)
                  ( A)
                  ( r)
                  ( s)
                  ( one-unital-associative-algebra-Commutative-Ring R A)))

  hom-ring-unital-associative-algebra-Commutative-Ring :
    hom-Ring
      ( ring-Commutative-Ring R)
      ( ring-unital-associative-algebra-Commutative-Ring R A)
  hom-ring-unital-associative-algebra-Commutative-Ring =
    ( ( map-hom-ring-unital-associative-algebra-Commutative-Ring ,
        preserves-add-hom-ring-unital-associative-algebra-Commutative-Ring
          ( _)
          ( _)) ,
      preserves-mul-hom-ring-unital-associative-algebra-Commutative-Ring _ _ ,
      preserves-one-hom-ring-unital-associative-algebra-Commutative-Ring)
```

### Given a unital associative algebra `A` over `R`, the ring homomorphism from `R` to `A` maps elements into the center of `A`

```agda
module _
  {l1 l2 : Level}
  (R : Commutative-Ring l1)
  (A : unital-associative-algebra-Commutative-Ring l2 R)
  where

  abstract
    is-central-map-hom-ring-unital-associative-algebra-Commutative-Ring :
      (r : type-Commutative-Ring R) →
      is-central-element-Ring
        ( ring-unital-associative-algebra-Commutative-Ring R A)
        ( map-hom-ring-unital-associative-algebra-Commutative-Ring R A r)
    is-central-map-hom-ring-unital-associative-algebra-Commutative-Ring r x =
      equational-reasoning
        mul-unital-associative-algebra-Commutative-Ring R A
          ( map-hom-ring-unital-associative-algebra-Commutative-Ring R A r)
          ( x)
        ＝
          scalar-mul-unital-associative-algebra-Commutative-Ring R A
            ( r)
            ( mul-unital-associative-algebra-Commutative-Ring R A
              ( one-unital-associative-algebra-Commutative-Ring R A)
              ( x))
          by
            associative-scalar-mul-mul-unital-associative-algebra-Commutative-Ring
              ( R)
              ( A)
              ( r)
              ( one-unital-associative-algebra-Commutative-Ring R A)
              ( x)
        ＝
          scalar-mul-unital-associative-algebra-Commutative-Ring R A
            ( r)
            ( mul-unital-associative-algebra-Commutative-Ring R A
              ( x)
              ( one-unital-associative-algebra-Commutative-Ring R A))
          by
            ap
              ( scalar-mul-unital-associative-algebra-Commutative-Ring R A r)
              ( is-central-element-unit-Monoid
                ( monoid-mul-unital-associative-algebra-Commutative-Ring R A)
                ( x))
        ＝
          mul-unital-associative-algebra-Commutative-Ring R A
            ( x)
            ( map-hom-ring-unital-associative-algebra-Commutative-Ring R A r)
          by
            left-swap-scalar-mul-mul-unital-associative-algebra-Commutative-Ring
              ( R)
              ( A)
              ( r)
              ( x)
              ( one-unital-associative-algebra-Commutative-Ring R A)
```
