# Function coherent H-spaces

```agda
module structured-types.function-coherent-h-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.unital-binary-operations
open import foundation.universe-levels

open import structured-types.coherent-h-spaces
open import structured-types.dependent-products-coherent-h-spaces
open import structured-types.pointed-types
```

</details>

## Idea

Given a [coherent H-space](structured-types.coherent-h-spaces.md) `M` and a type
`I`, the **function coherent H-space** `M^I` consists of functions from `I` to
the underlying type of `M`. Every component of the structure is given pointwise.

## Definition

```agda
module _
  {l1 l2 : Level} (I : UU l1) (M : Coherent-H-Space l2)
  where

  function-Coherent-H-Space : Coherent-H-Space (l1 ⊔ l2)
  function-Coherent-H-Space = Π-Coherent-H-Space I (λ _ → M)

  pointed-type-function-Coherent-H-Space : Pointed-Type (l1 ⊔ l2)
  pointed-type-function-Coherent-H-Space =
    pointed-type-Coherent-H-Space function-Coherent-H-Space

  type-function-Coherent-H-Space : UU (l1 ⊔ l2)
  type-function-Coherent-H-Space =
    type-Coherent-H-Space function-Coherent-H-Space

  unit-function-Coherent-H-Space : type-function-Coherent-H-Space
  unit-function-Coherent-H-Space =
    unit-Coherent-H-Space function-Coherent-H-Space

  mul-function-Coherent-H-Space :
    type-function-Coherent-H-Space →
    type-function-Coherent-H-Space →
    type-function-Coherent-H-Space
  mul-function-Coherent-H-Space = mul-Coherent-H-Space function-Coherent-H-Space

  left-unit-law-mul-function-Coherent-H-Space :
    (f : type-function-Coherent-H-Space) →
    mul-function-Coherent-H-Space unit-function-Coherent-H-Space f ＝ f
  left-unit-law-mul-function-Coherent-H-Space =
    left-unit-law-mul-Coherent-H-Space function-Coherent-H-Space

  right-unit-law-mul-function-Coherent-H-Space :
    (f : type-function-Coherent-H-Space) →
    mul-function-Coherent-H-Space f unit-function-Coherent-H-Space ＝ f
  right-unit-law-mul-function-Coherent-H-Space =
    right-unit-law-mul-Coherent-H-Space function-Coherent-H-Space

  is-unital-mul-function-Coherent-H-Space :
    is-unital mul-function-Coherent-H-Space
  is-unital-mul-function-Coherent-H-Space =
    is-unital-mul-Coherent-H-Space function-Coherent-H-Space

  coh-unit-laws-mul-function-Coherent-H-Space :
    coh-unit-laws
      ( mul-function-Coherent-H-Space)
      ( unit-function-Coherent-H-Space)
      ( left-unit-law-mul-function-Coherent-H-Space)
      ( right-unit-law-mul-function-Coherent-H-Space)
  coh-unit-laws-mul-function-Coherent-H-Space =
    coh-unit-laws-mul-Coherent-H-Space function-Coherent-H-Space

  coherent-unit-laws-mul-function-Coherent-H-Space :
    coherent-unit-laws
      ( mul-function-Coherent-H-Space)
      ( unit-function-Coherent-H-Space)
  coherent-unit-laws-mul-function-Coherent-H-Space =
    coherent-unit-laws-mul-Coherent-H-Space function-Coherent-H-Space

  is-coherently-unital-mul-function-Coherent-H-Space :
    is-coherently-unital mul-function-Coherent-H-Space
  is-coherently-unital-mul-function-Coherent-H-Space =
    is-coherently-unital-mul-Coherent-H-Space function-Coherent-H-Space

  coherent-unital-mul-function-Coherent-H-Space :
    coherent-unital-mul-Pointed-Type pointed-type-function-Coherent-H-Space
  coherent-unital-mul-function-Coherent-H-Space =
    coherent-unital-mul-Coherent-H-Space function-Coherent-H-Space
```
