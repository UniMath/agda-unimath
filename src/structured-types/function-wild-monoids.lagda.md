# Function wild monoids

```agda
module structured-types.function-wild-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-types
open import foundation.universe-levels

open import structured-types.dependent-products-wild-monoids
open import structured-types.h-spaces
open import structured-types.pointed-types
open import structured-types.wild-monoids
```

</details>

## Idea

Given a [wild monoid](structured-types.wild-monoids.md) `M` and a type `I`, the
{{#concept "function wild monoid" Agda=function-Wild-Monoid}} `M^I` consists of
functions from `I` to the underlying type of `M`. Every component of the
structure is given pointwise.

## Definition

```agda
module _
  {l1 l2 : Level} (I : UU l1) (M : Wild-Monoid l2)
  where

  function-Wild-Monoid : Wild-Monoid (l1 ⊔ l2)
  function-Wild-Monoid = Π-Wild-Monoid I (λ _ → M)

  h-space-function-Wild-Monoid : H-Space (l1 ⊔ l2)
  h-space-function-Wild-Monoid =
      h-space-Wild-Monoid function-Wild-Monoid

  pointed-type-function-Wild-Monoid : Pointed-Type (l1 ⊔ l2)
  pointed-type-function-Wild-Monoid =
    pointed-type-Wild-Monoid function-Wild-Monoid

  type-function-Wild-Monoid : UU (l1 ⊔ l2)
  type-function-Wild-Monoid = type-Wild-Monoid function-Wild-Monoid

  unit-function-Wild-Monoid : type-function-Wild-Monoid
  unit-function-Wild-Monoid = unit-Wild-Monoid function-Wild-Monoid

  mul-function-Wild-Monoid :
    type-function-Wild-Monoid →
    type-function-Wild-Monoid →
    type-function-Wild-Monoid
  mul-function-Wild-Monoid = mul-Wild-Monoid function-Wild-Monoid

  left-unit-law-mul-function-Wild-Monoid :
    ( f : type-function-Wild-Monoid) →
    ( mul-function-Wild-Monoid (unit-function-Wild-Monoid) f) ＝ f
  left-unit-law-mul-function-Wild-Monoid =
    left-unit-law-mul-Wild-Monoid function-Wild-Monoid

  right-unit-law-mul-function-Wild-Monoid :
    ( f : type-function-Wild-Monoid) →
    ( mul-function-Wild-Monoid f (unit-function-Wild-Monoid)) ＝ f
  right-unit-law-mul-function-Wild-Monoid =
    right-unit-law-mul-Wild-Monoid function-Wild-Monoid

  associator-function-Wild-Monoid :
    associator-H-Space h-space-function-Wild-Monoid
  associator-function-Wild-Monoid = associator-Wild-Monoid function-Wild-Monoid

  unital-associator-function-Wild-Monoid :
    unital-associator (h-space-Wild-Monoid function-Wild-Monoid)
  unital-associator-function-Wild-Monoid =
    unital-associator-Wild-Monoid function-Wild-Monoid
```
