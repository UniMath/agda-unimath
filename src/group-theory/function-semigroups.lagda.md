# Function semigroups

```agda
module group-theory.function-semigroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.semigroups
```

<details>

## Idea

Given a semigroup `G` and a type `X`, the function semigroup `G^X`
consists of functions from `X` to the underlying type of `G`. The
semigroup operation is given pointwise.

## Definition

```agda
module _
  {l1 l2 : Level} (G : Semigroup l1) (X : UU l2)
  where

  set-function-Semigroup : Set (l1 ⊔ l2)
  set-function-Semigroup = function-Set X (set-Semigroup G)

  type-function-Semigroup : UU (l1 ⊔ l2)
  type-function-Semigroup = type-Set set-function-Semigroup

  mul-function-Semigroup :
    (f g : type-function-Semigroup) → type-function-Semigroup
  mul-function-Semigroup f g x = mul-Semigroup G (f x) (g x)

  associative-mul-function-Semigroup :
    (f g h : type-function-Semigroup) →
    mul-function-Semigroup (mul-function-Semigroup f g) h ＝
    mul-function-Semigroup f (mul-function-Semigroup g h)
  associative-mul-function-Semigroup f g h =
    eq-htpy (λ x → associative-mul-Semigroup G (f x) (g x) (h x))

  has-associative-mul-function-Semigroup :
    has-associative-mul-Set set-function-Semigroup
  pr1 has-associative-mul-function-Semigroup =
    mul-function-Semigroup
  pr2 has-associative-mul-function-Semigroup =
    associative-mul-function-Semigroup

  function-Semigroup : Semigroup (l1 ⊔ l2)
  pr1 function-Semigroup = set-function-Semigroup
  pr2 function-Semigroup = has-associative-mul-function-Semigroup
```
