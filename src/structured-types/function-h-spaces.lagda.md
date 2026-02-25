# Function H-spaces

```agda
module structured-types.function-h-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-types
open import foundation.unital-binary-operations
open import foundation.universe-levels

open import structured-types.dependent-products-h-spaces
open import structured-types.h-spaces
open import structured-types.pointed-types
```

</details>

## Idea

Given a [H-space](structured-types.h-spaces.md) `M` and a type `I`, the
{{#concept "function H-space" Agda=function-H-Space}} `M^I` consists of
functions from `I` to the underlying type of `M`. Every component of the
structure is given pointwise.

## Definition

```agda
module _
  {l1 l2 : Level} (I : UU l1) (M : H-Space l2)
  where

  function-H-Space : H-Space (l1 ⊔ l2)
  function-H-Space = Π-H-Space I (λ _ → M)

  pointed-type-function-H-Space : Pointed-Type (l1 ⊔ l2)
  pointed-type-function-H-Space =
    pointed-type-H-Space function-H-Space

  type-function-H-Space : UU (l1 ⊔ l2)
  type-function-H-Space =
    type-H-Space function-H-Space

  unit-function-H-Space : type-function-H-Space
  unit-function-H-Space =
    unit-H-Space function-H-Space

  mul-function-H-Space :
    type-function-H-Space →
    type-function-H-Space →
    type-function-H-Space
  mul-function-H-Space = mul-H-Space function-H-Space

  left-unit-law-mul-function-H-Space :
    (f : type-function-H-Space) →
    mul-function-H-Space unit-function-H-Space f ＝ f
  left-unit-law-mul-function-H-Space =
    left-unit-law-mul-H-Space function-H-Space

  right-unit-law-mul-function-H-Space :
    (f : type-function-H-Space) →
    mul-function-H-Space f unit-function-H-Space ＝ f
  right-unit-law-mul-function-H-Space =
    right-unit-law-mul-H-Space function-H-Space

  is-unital-mul-function-H-Space :
    is-unital mul-function-H-Space
  is-unital-mul-function-H-Space =
    is-unital-mul-H-Space function-H-Space

  coh-unit-laws-mul-function-H-Space :
    coh-unit-laws
      ( mul-function-H-Space)
      ( unit-function-H-Space)
      ( left-unit-law-mul-function-H-Space)
      ( right-unit-law-mul-function-H-Space)
  coh-unit-laws-mul-function-H-Space =
    coh-unit-laws-mul-H-Space function-H-Space

  coherent-unit-laws-mul-function-H-Space :
    coherent-unit-laws
      ( mul-function-H-Space)
      ( unit-function-H-Space)
  coherent-unit-laws-mul-function-H-Space =
    coherent-unit-laws-mul-H-Space function-H-Space

  is-coherently-unital-mul-function-H-Space :
    is-coherently-unital mul-function-H-Space
  is-coherently-unital-mul-function-H-Space =
    is-coherently-unital-mul-H-Space function-H-Space

  coherent-unital-mul-function-H-Space :
    coherent-unital-mul-Pointed-Type pointed-type-function-H-Space
  coherent-unital-mul-function-H-Space =
    coherent-unital-mul-H-Space function-H-Space
```
