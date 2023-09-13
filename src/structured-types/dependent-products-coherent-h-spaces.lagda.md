# Dependent products of coherent H-spaces

```agda
module structured-types.dependent-products-coherent-h-spaces where
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
open import structured-types.pointed-types
```

</details>

## Idea

Given a family of [coherent H-spaces](structured-types.coherent-h-spaces.md)
`Mᵢ` indexed by `i : I`, the dependent product `Π(i : I), Mᵢ` is a coherent
H-space consisting of dependent functions taking `i : I` to an element of the
underlying type of `Mᵢ`. The multiplicative operation and the unit are given
pointwise.

## Definition

```agda
module _
  {l1 l2 : Level} (I : UU l1) (M : I → Coherent-H-Space l2)
  where

  pointed-type-Π-Coherent-H-Space : Pointed-Type (l1 ⊔ l2)
  pointed-type-Π-Coherent-H-Space =
    Π-Pointed-Type I (λ x → pointed-type-Coherent-H-Space (M x))

  type-Π-Coherent-H-Space : UU (l1 ⊔ l2)
  type-Π-Coherent-H-Space = type-Pointed-Type pointed-type-Π-Coherent-H-Space

  unit-Π-Coherent-H-Space : type-Π-Coherent-H-Space
  unit-Π-Coherent-H-Space = point-Pointed-Type (pointed-type-Π-Coherent-H-Space)

  mul-Π-Coherent-H-Space :
    type-Π-Coherent-H-Space → type-Π-Coherent-H-Space → type-Π-Coherent-H-Space
  mul-Π-Coherent-H-Space f g i = mul-Coherent-H-Space (M i) (f i) (g i)

  left-unit-law-mul-Π-Coherent-H-Space :
    (f : type-Π-Coherent-H-Space) →
    mul-Π-Coherent-H-Space unit-Π-Coherent-H-Space f ＝ f
  left-unit-law-mul-Π-Coherent-H-Space f =
    eq-htpy (λ i → left-unit-law-mul-Coherent-H-Space (M i) (f i))

  right-unit-law-mul-Π-Coherent-H-Space :
    (f : type-Π-Coherent-H-Space) →
    mul-Π-Coherent-H-Space f unit-Π-Coherent-H-Space ＝ f
  right-unit-law-mul-Π-Coherent-H-Space f =
    eq-htpy (λ i → right-unit-law-mul-Coherent-H-Space (M i) (f i))

  is-unital-mul-Π-Coherent-H-Space : is-unital mul-Π-Coherent-H-Space
  pr1 is-unital-mul-Π-Coherent-H-Space = unit-Π-Coherent-H-Space
  pr1 (pr2 is-unital-mul-Π-Coherent-H-Space) =
    left-unit-law-mul-Π-Coherent-H-Space
  pr2 (pr2 is-unital-mul-Π-Coherent-H-Space) =
    right-unit-law-mul-Π-Coherent-H-Space

  coh-unit-laws-mul-Π-Coherent-H-Space :
    coh-unit-laws
      ( mul-Π-Coherent-H-Space)
      ( unit-Π-Coherent-H-Space)
      ( left-unit-law-mul-Π-Coherent-H-Space)
      ( right-unit-law-mul-Π-Coherent-H-Space)
  coh-unit-laws-mul-Π-Coherent-H-Space =
    ap eq-htpy (eq-htpy (λ i → coh-unit-laws-mul-Coherent-H-Space (M i)))

  coherent-unit-laws-mul-Π-Coherent-H-Space :
    coherent-unit-laws mul-Π-Coherent-H-Space unit-Π-Coherent-H-Space
  pr1 coherent-unit-laws-mul-Π-Coherent-H-Space =
    left-unit-law-mul-Π-Coherent-H-Space
  pr1 (pr2 coherent-unit-laws-mul-Π-Coherent-H-Space) =
    right-unit-law-mul-Π-Coherent-H-Space
  pr2 (pr2 coherent-unit-laws-mul-Π-Coherent-H-Space) =
    coh-unit-laws-mul-Π-Coherent-H-Space

  is-coherently-unital-mul-Π-Coherent-H-Space :
    is-coherently-unital mul-Π-Coherent-H-Space
  pr1 is-coherently-unital-mul-Π-Coherent-H-Space = unit-Π-Coherent-H-Space
  pr2 is-coherently-unital-mul-Π-Coherent-H-Space =
    coherent-unit-laws-mul-Π-Coherent-H-Space

  coherent-unital-mul-Π-Coherent-H-Space :
    coherent-unital-mul-Pointed-Type pointed-type-Π-Coherent-H-Space
  pr1 coherent-unital-mul-Π-Coherent-H-Space = mul-Π-Coherent-H-Space
  pr2 coherent-unital-mul-Π-Coherent-H-Space =
    coherent-unit-laws-mul-Π-Coherent-H-Space

  Π-Coherent-H-Space : Coherent-H-Space (l1 ⊔ l2)
  pr1 Π-Coherent-H-Space = pointed-type-Π-Coherent-H-Space
  pr2 Π-Coherent-H-Space = coherent-unital-mul-Π-Coherent-H-Space
```
