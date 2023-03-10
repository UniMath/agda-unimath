# Function groups

```agda
module group-theory.function-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.function-semigroups
open import group-theory.groups
open import group-theory.monoids
open import group-theory.semigroups
```

<details>

## Idea

Given a group `G` and a type `X`, the function group `G^X`
consists of functions from `X` to the underlying type of `G`. The
group operations are given pointwise.

## Definition

```agda
module _
  {l1 l2 : Level} (G : Group l1) (X : UU l2)
  where

  semigroup-function-Group : Semigroup (l1 ⊔ l2)
  semigroup-function-Group =
    function-Semigroup (semigroup-Group G) X

  set-function-Group : Set (l1 ⊔ l2)
  set-function-Group = set-Semigroup semigroup-function-Group

  type-function-Group : UU (l1 ⊔ l2)
  type-function-Group = type-Semigroup semigroup-function-Group

  mul-function-Group :
    (f g : type-function-Group) → type-function-Group
  mul-function-Group = mul-Semigroup semigroup-function-Group

  associative-mul-function-Group :
    (f g h : type-function-Group) →
    mul-function-Group (mul-function-Group f g) h ＝
    mul-function-Group f (mul-function-Group g h)
  associative-mul-function-Group =
    associative-mul-Semigroup semigroup-function-Group

  unit-function-Group : type-function-Group
  unit-function-Group x = unit-Group G

  left-unit-law-mul-function-Group :
    (f : type-function-Group) →
    mul-function-Group unit-function-Group f ＝ f
  left-unit-law-mul-function-Group f =
    eq-htpy (λ x → left-unit-law-mul-Group G (f x))

  right-unit-law-mul-function-Group :
    (f : type-function-Group) →
    mul-function-Group f unit-function-Group ＝ f
  right-unit-law-mul-function-Group f =
    eq-htpy (λ x → right-unit-law-mul-Group G (f x))

  is-unital-function-Group :
    is-unital-Semigroup semigroup-function-Group
  pr1 is-unital-function-Group =
    unit-function-Group
  pr1 (pr2 is-unital-function-Group) =
    left-unit-law-mul-function-Group
  pr2 (pr2 is-unital-function-Group) =
    right-unit-law-mul-function-Group

  monoid-function-Group : Monoid (l1 ⊔ l2)
  pr1 monoid-function-Group = semigroup-function-Group
  pr2 monoid-function-Group = is-unital-function-Group

  inv-function-Group : type-function-Group → type-function-Group
  inv-function-Group f x = inv-Group G (f x)

  left-inverse-law-mul-function-Group :
    (f : type-function-Group) →
    mul-function-Group (inv-function-Group f) f ＝ unit-function-Group
  left-inverse-law-mul-function-Group f =
    eq-htpy (λ x → left-inverse-law-mul-Group G (f x))

  right-inverse-law-mul-function-Group :
    (f : type-function-Group) →
    mul-function-Group f (inv-function-Group f) ＝ unit-function-Group
  right-inverse-law-mul-function-Group f =
    eq-htpy (λ x → right-inverse-law-mul-Group G (f x))

  is-group-function-Group : is-group semigroup-function-Group
  pr1 is-group-function-Group = is-unital-function-Group
  pr1 (pr2 is-group-function-Group) = inv-function-Group
  pr1 (pr2 (pr2 is-group-function-Group)) =
    left-inverse-law-mul-function-Group
  pr2 (pr2 (pr2 is-group-function-Group)) =
    right-inverse-law-mul-function-Group

  function-Group : Group (l1 ⊔ l2)
  pr1 function-Group = semigroup-function-Group
  pr2 function-Group = is-group-function-Group
```
