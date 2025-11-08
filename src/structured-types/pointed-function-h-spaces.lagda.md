# Pointed function H-spaces

```agda
module structured-types.pointed-function-h-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-types
open import foundation.unital-binary-operations
open import foundation.universe-levels

open import structured-types.h-spaces
open import structured-types.pointed-dependent-function-h-spaces
open import structured-types.pointed-types
```

</details>

## Idea

Given a [H-space](structured-types.h-spaces.md) `M` and a
[pointed type](structured-types.pointed-types.md) `I`, the
{{#concept "pointed function H-space" Agda=pointed-function-H-Space}} `I →∗ M`
consists of [pointed functions](structured-types.pointed-maps.md) from `I` to
the underlying pointed type of `M`. The multiplication is given pointwise, and
at the base point by the
[binary action on identifications](foundation.action-on-identifications-binary-functions.md)
of the multiplication operation of `M`.

## Definition

```agda
module _
  {l1 l2 : Level} (I∗ : Pointed-Type l1) (M : H-Space l2)
  where

  pointed-function-H-Space : H-Space (l1 ⊔ l2)
  pointed-function-H-Space = pointed-Π-H-Space I∗ (λ _ → M)

  pointed-type-pointed-function-H-Space : Pointed-Type (l1 ⊔ l2)
  pointed-type-pointed-function-H-Space =
    pointed-type-H-Space pointed-function-H-Space

  type-pointed-function-H-Space : UU (l1 ⊔ l2)
  type-pointed-function-H-Space =
    type-H-Space pointed-function-H-Space

  unit-pointed-function-H-Space : type-pointed-function-H-Space
  unit-pointed-function-H-Space =
    unit-H-Space pointed-function-H-Space

  mul-pointed-function-H-Space :
    type-pointed-function-H-Space →
    type-pointed-function-H-Space →
    type-pointed-function-H-Space
  mul-pointed-function-H-Space = mul-H-Space pointed-function-H-Space

  left-unit-law-mul-pointed-function-H-Space :
    (f : type-pointed-function-H-Space) →
    mul-pointed-function-H-Space unit-pointed-function-H-Space f ＝ f
  left-unit-law-mul-pointed-function-H-Space =
    left-unit-law-mul-H-Space pointed-function-H-Space

  right-unit-law-mul-pointed-function-H-Space :
    (f : type-pointed-function-H-Space) →
    mul-pointed-function-H-Space f unit-pointed-function-H-Space ＝ f
  right-unit-law-mul-pointed-function-H-Space =
    right-unit-law-mul-H-Space pointed-function-H-Space

  is-unital-mul-pointed-function-H-Space :
    is-unital mul-pointed-function-H-Space
  is-unital-mul-pointed-function-H-Space =
    is-unital-mul-H-Space pointed-function-H-Space

  coh-unit-laws-mul-pointed-function-H-Space :
    coh-unit-laws
      ( mul-pointed-function-H-Space)
      ( unit-pointed-function-H-Space)
      ( left-unit-law-mul-pointed-function-H-Space)
      ( right-unit-law-mul-pointed-function-H-Space)
  coh-unit-laws-mul-pointed-function-H-Space =
    coh-unit-laws-mul-H-Space pointed-function-H-Space

  coherent-unit-laws-mul-pointed-function-H-Space :
    coherent-unit-laws
      ( mul-pointed-function-H-Space)
      ( unit-pointed-function-H-Space)
  coherent-unit-laws-mul-pointed-function-H-Space =
    coherent-unit-laws-mul-H-Space pointed-function-H-Space

  is-coherently-unital-mul-pointed-function-H-Space :
    is-coherently-unital mul-pointed-function-H-Space
  is-coherently-unital-mul-pointed-function-H-Space =
    is-coherently-unital-mul-H-Space pointed-function-H-Space

  coherent-unital-mul-pointed-function-H-Space :
    coherent-unital-mul-Pointed-Type pointed-type-pointed-function-H-Space
  coherent-unital-mul-pointed-function-H-Space =
    coherent-unital-mul-H-Space pointed-function-H-Space
```
