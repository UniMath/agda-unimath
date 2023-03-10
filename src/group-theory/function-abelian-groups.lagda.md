# Function groups of abelian groups

```agda
module group-theory.function-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.function-groups
open import group-theory.groups
open import group-theory.monoids
open import group-theory.semigroups
```

<details>

## Idea

Given an abelian group `G` and a type `X`, the function group `G^X`
consists of functions from `X` to the underlying type of `G`. The
group operations are given pointwise.

## Definition

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (X : UU l2)
  where

  group-function-Ab : Group (l1 ⊔ l2)
  group-function-Ab = function-Group (group-Ab A) X

  semigroup-function-Ab : Semigroup (l1 ⊔ l2)
  semigroup-function-Ab = semigroup-function-Group (group-Ab A) X

  set-function-Ab : Set (l1 ⊔ l2)
  set-function-Ab = set-Semigroup semigroup-function-Ab

  type-function-Ab : UU (l1 ⊔ l2)
  type-function-Ab = type-Semigroup semigroup-function-Ab

  add-function-Ab :
    (f g : type-function-Ab) → type-function-Ab
  add-function-Ab = mul-Semigroup semigroup-function-Ab

  associative-add-function-Ab :
    (f g h : type-function-Ab) →
    add-function-Ab (add-function-Ab f g) h ＝
    add-function-Ab f (add-function-Ab g h)
  associative-add-function-Ab =
    associative-mul-Semigroup semigroup-function-Ab

  zero-function-Ab : type-function-Ab
  zero-function-Ab x = zero-Ab A

  left-unit-law-add-function-Ab :
    (f : type-function-Ab) →
    add-function-Ab zero-function-Ab f ＝ f
  left-unit-law-add-function-Ab =
    left-unit-law-mul-function-Group (group-Ab A) X

  right-unit-law-add-function-Ab :
    (f : type-function-Ab) →
    add-function-Ab f zero-function-Ab ＝ f
  right-unit-law-add-function-Ab =
    right-unit-law-mul-function-Group (group-Ab A) X

  monoid-function-Ab : Monoid (l1 ⊔ l2)
  monoid-function-Ab = monoid-function-Group (group-Ab A) X

  neg-function-Ab : type-function-Ab → type-function-Ab
  neg-function-Ab = inv-function-Group (group-Ab A) X

  left-inverse-law-add-function-Ab :
    (f : type-function-Ab) →
    add-function-Ab (neg-function-Ab f) f ＝ zero-function-Ab
  left-inverse-law-add-function-Ab =
    left-inverse-law-mul-function-Group (group-Ab A) X

  right-inverse-law-add-function-Ab :
    (f : type-function-Ab) →
    add-function-Ab f (neg-function-Ab f) ＝ zero-function-Ab
  right-inverse-law-add-function-Ab =
    right-inverse-law-mul-function-Group (group-Ab A) X

  commutative-add-function-Ab :
    (f g : type-function-Ab) →
    add-function-Ab f g ＝ add-function-Ab g f
  commutative-add-function-Ab f g =
    eq-htpy (λ x → commutative-add-Ab A (f x) (g x))

  function-Ab : Ab (l1 ⊔ l2)
  pr1 function-Ab = group-function-Ab
  pr2 function-Ab = commutative-add-function-Ab
```
