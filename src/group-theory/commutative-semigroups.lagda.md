# Commutative semigroups

```agda
module group-theory.commutative-semigroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.interchange-law
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.semigroups
```

</details>

## Idea

A
{{#concept "commutative semigroup" WDID=Q27672715 WD="commutative semigroup" Agda=Commutative-Semigroup}}
is a [semigroup](group-theory.semigroups.md) `G` in which `xy = yx` for all
`x y : G`.

## Definition

```agda
module _
  {l : Level} (G : Semigroup l)
  where

  is-commutative-prop-Semigroup : Prop l
  is-commutative-prop-Semigroup =
    Π-Prop
      ( type-Semigroup G)
      ( λ x →
        Π-Prop
          ( type-Semigroup G)
          ( λ y →
            Id-Prop
              ( set-Semigroup G)
              ( mul-Semigroup G x y)
              ( mul-Semigroup G y x)))

  is-commutative-Semigroup : UU l
  is-commutative-Semigroup = type-Prop is-commutative-prop-Semigroup

Commutative-Semigroup : (l : Level) → UU (lsuc l)
Commutative-Semigroup l = type-subtype (is-commutative-prop-Semigroup {l})

module _
  {l : Level} (G : Commutative-Semigroup l)
  where

  semigroup-Commutative-Semigroup : Semigroup l
  semigroup-Commutative-Semigroup = pr1 G

  commutative-mul-Commutative-Semigroup :
    is-commutative-Semigroup semigroup-Commutative-Semigroup
  commutative-mul-Commutative-Semigroup = pr2 G

  type-Commutative-Semigroup : UU l
  type-Commutative-Semigroup = type-Semigroup semigroup-Commutative-Semigroup

  set-Commutative-Semigroup : Set l
  set-Commutative-Semigroup = set-Semigroup semigroup-Commutative-Semigroup

  mul-Commutative-Semigroup :
    type-Commutative-Semigroup → type-Commutative-Semigroup →
    type-Commutative-Semigroup
  mul-Commutative-Semigroup = mul-Semigroup semigroup-Commutative-Semigroup

  mul-Commutative-Semigroup' :
    type-Commutative-Semigroup → type-Commutative-Semigroup →
    type-Commutative-Semigroup
  mul-Commutative-Semigroup' y x = mul-Commutative-Semigroup x y

  ap-mul-Commutative-Semigroup :
    {x x' y y' : type-Commutative-Semigroup} →
    x ＝ x' → y ＝ y' →
    mul-Commutative-Semigroup x y ＝ mul-Commutative-Semigroup x' y'
  ap-mul-Commutative-Semigroup =
    ap-mul-Semigroup semigroup-Commutative-Semigroup

  associative-mul-Commutative-Semigroup :
    (x y z : type-Commutative-Semigroup) →
    mul-Commutative-Semigroup (mul-Commutative-Semigroup x y) z ＝
    mul-Commutative-Semigroup x (mul-Commutative-Semigroup y z)
  associative-mul-Commutative-Semigroup =
    associative-mul-Semigroup semigroup-Commutative-Semigroup

  interchange-mul-mul-Commutative-Semigroup :
    (a b c d : type-Commutative-Semigroup) →
    mul-Commutative-Semigroup
      ( mul-Commutative-Semigroup a b)
      ( mul-Commutative-Semigroup c d) ＝
    mul-Commutative-Semigroup
      ( mul-Commutative-Semigroup a c)
      ( mul-Commutative-Semigroup b d)
  interchange-mul-mul-Commutative-Semigroup =
    interchange-law-commutative-and-associative
      mul-Commutative-Semigroup
      commutative-mul-Commutative-Semigroup
      associative-mul-Commutative-Semigroup

  right-swap-mul-Commutative-Semigroup :
    (x y z : type-Commutative-Semigroup) →
    mul-Commutative-Semigroup
      ( mul-Commutative-Semigroup x y)
      ( z) ＝
    mul-Commutative-Semigroup
      ( mul-Commutative-Semigroup x z)
      ( y)
  right-swap-mul-Commutative-Semigroup x y z =
    ( associative-mul-Commutative-Semigroup x y z) ∙
    ( ap
      ( mul-Commutative-Semigroup x)
      ( commutative-mul-Commutative-Semigroup y z)) ∙
    ( inv (associative-mul-Commutative-Semigroup x z y))

  left-swap-mul-Commutative-Semigroup :
    (x y z : type-Commutative-Semigroup) →
    mul-Commutative-Semigroup
      ( x)
      ( mul-Commutative-Semigroup y z) ＝
    mul-Commutative-Semigroup
      ( y)
      ( mul-Commutative-Semigroup x z)
  left-swap-mul-Commutative-Semigroup x y z =
    inv (associative-mul-Commutative-Semigroup x y z) ∙
    ap
      ( mul-Commutative-Semigroup' z)
      ( commutative-mul-Commutative-Semigroup x y) ∙
    associative-mul-Commutative-Semigroup y x z
```
