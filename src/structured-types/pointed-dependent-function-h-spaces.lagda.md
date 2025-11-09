# Pointed dependent function H-spaces

```agda
module structured-types.pointed-dependent-function-h-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.unital-binary-operations
open import foundation.universe-levels

open import structured-types.h-spaces
open import structured-types.magmas
open import structured-types.noncoherent-h-spaces
open import structured-types.pointed-dependent-functions
open import structured-types.pointed-homotopies
open import structured-types.pointed-types
```

</details>

## Idea

Given a family of [H-spaces](structured-types.h-spaces.md) `M i` indexed by a
[pointed type](structured-types.pointed-types.md) `i∗ : I`, the
{{#concept "pointed dependent functions" Disambiguation="H-space" Agda=pointed-Π-H-Space}}
`Π∗(i : I), M i` is an H-space consisting of
[pointed dependent functions](structured-types.pointed-dependent-functions.md)
taking `i : I` to an element of the underlying type of `M i`, and taking `i∗` to
the unit of `M i∗`. The multiplication is given pointwise, and at the base point
by the
[binary action on identifications](foundation.action-on-identifications-binary-functions.md)
of the multiplication operation of `M i∗`.

## Definition

```agda
module _
  {l1 l2 : Level} (I∗ : Pointed-Type l1)
  (let I = type-Pointed-Type I∗)
  (let i∗ = point-Pointed-Type I∗)
  (M : I → H-Space l2)
  where

  type-pointed-Π-H-Space : UU (l1 ⊔ l2)
  type-pointed-Π-H-Space = Π∗ I∗ (type-H-Space ∘ M , unit-H-Space (M i∗))

  unit-pointed-Π-H-Space : type-pointed-Π-H-Space
  unit-pointed-Π-H-Space = (unit-H-Space ∘ M , refl)

  pointed-type-pointed-Π-H-Space : Pointed-Type (l1 ⊔ l2)
  pointed-type-pointed-Π-H-Space =
    ( type-pointed-Π-H-Space , unit-pointed-Π-H-Space)

  mul-pointed-Π-H-Space :
    type-pointed-Π-H-Space → type-pointed-Π-H-Space → type-pointed-Π-H-Space
  pr1 (mul-pointed-Π-H-Space (f , f∗) (g , g∗)) i =
    mul-H-Space (M i) (f i) (g i)
  pr2 (mul-pointed-Π-H-Space (f , f∗) (g , g∗)) =
    ( ap-binary (mul-H-Space (M i∗)) f∗ g∗) ∙
    ( left-unit-law-mul-H-Space (M i∗) (unit-H-Space (M i∗)))

  pointed-htpy-left-unit-law-mul-pointed-Π-H-Space :
    (f : type-pointed-Π-H-Space) →
    mul-pointed-Π-H-Space unit-pointed-Π-H-Space f ~∗ f
  pr1 (pointed-htpy-left-unit-law-mul-pointed-Π-H-Space (f , f∗)) i =
    left-unit-law-mul-H-Space (M i) (f i)
  pr2 (pointed-htpy-left-unit-law-mul-pointed-Π-H-Space (f , f∗)) =
    inv-nat-htpy-id (left-unit-law-mul-H-Space (M i∗)) f∗

  left-unit-law-mul-pointed-Π-H-Space :
    (f : type-pointed-Π-H-Space) →
    mul-pointed-Π-H-Space unit-pointed-Π-H-Space f ＝ f
  left-unit-law-mul-pointed-Π-H-Space f =
    eq-pointed-htpy
      ( mul-pointed-Π-H-Space unit-pointed-Π-H-Space f)
      ( f)
      ( pointed-htpy-left-unit-law-mul-pointed-Π-H-Space f)

  pointed-htpy-right-unit-law-mul-pointed-Π-H-Space' :
    (f : type-pointed-Π-H-Space) →
    mul-pointed-Π-H-Space f unit-pointed-Π-H-Space ~∗ f
  pr1 (pointed-htpy-right-unit-law-mul-pointed-Π-H-Space' (f , f∗)) i =
    right-unit-law-mul-H-Space (M i) (f i)
  pr2 (pointed-htpy-right-unit-law-mul-pointed-Π-H-Space' (f , f∗)) =
    equational-reasoning
      (ap (λ f → mul-H-Space (M i∗) f (unit-H-Space (M i∗))) f∗ ∙ refl) ∙
      left-unit-law-mul-H-Space (M i∗) (unit-H-Space (M i∗))
      ＝ ap (λ f → mul-H-Space (M i∗) f (unit-H-Space (M i∗))) f∗ ∙
        right-unit-law-mul-H-Space (M i∗) (unit-H-Space (M i∗))
        by ap-binary (_∙_) right-unit (coh-unit-laws-mul-H-Space (M i∗))
      ＝ right-unit-law-mul-H-Space (M i∗) (f i∗) ∙ f∗
        by inv-nat-htpy-id (right-unit-law-mul-H-Space (M i∗)) f∗

  right-unit-law-mul-pointed-Π-H-Space' :
    (f : type-pointed-Π-H-Space) →
    mul-pointed-Π-H-Space f unit-pointed-Π-H-Space ＝ f
  right-unit-law-mul-pointed-Π-H-Space' f =
    eq-pointed-htpy
      ( mul-pointed-Π-H-Space f unit-pointed-Π-H-Space)
      ( f)
      ( pointed-htpy-right-unit-law-mul-pointed-Π-H-Space' f)

  noncoherent-h-space-pointed-Π-H-Space : Noncoherent-H-Space (l1 ⊔ l2)
  noncoherent-h-space-pointed-Π-H-Space =
    ( pointed-type-pointed-Π-H-Space ,
      mul-pointed-Π-H-Space ,
      left-unit-law-mul-pointed-Π-H-Space ,
      right-unit-law-mul-pointed-Π-H-Space')

  pointed-Π-H-Space : H-Space (l1 ⊔ l2)
  pointed-Π-H-Space =
    h-space-Noncoherent-H-Space noncoherent-h-space-pointed-Π-H-Space

  right-unit-law-mul-pointed-Π-H-Space :
    (f : type-pointed-Π-H-Space) →
    mul-pointed-Π-H-Space f unit-pointed-Π-H-Space ＝ f
  right-unit-law-mul-pointed-Π-H-Space =
    right-unit-law-mul-H-Space pointed-Π-H-Space

  is-unital-mul-pointed-Π-H-Space : is-unital mul-pointed-Π-H-Space
  is-unital-mul-pointed-Π-H-Space = is-unital-mul-H-Space pointed-Π-H-Space

  coh-unit-laws-mul-pointed-Π-H-Space :
    coh-unit-laws
      ( mul-pointed-Π-H-Space)
      ( unit-pointed-Π-H-Space)
      ( left-unit-law-mul-pointed-Π-H-Space)
      ( right-unit-law-mul-pointed-Π-H-Space)
  coh-unit-laws-mul-pointed-Π-H-Space =
    coh-unit-laws-mul-H-Space pointed-Π-H-Space

  coherent-unit-laws-mul-pointed-Π-H-Space :
    coherent-unit-laws mul-pointed-Π-H-Space unit-pointed-Π-H-Space
  coherent-unit-laws-mul-pointed-Π-H-Space =
    coherent-unit-laws-mul-H-Space pointed-Π-H-Space

  is-coherently-unital-mul-pointed-Π-H-Space :
    is-coherently-unital mul-pointed-Π-H-Space
  is-coherently-unital-mul-pointed-Π-H-Space =
    is-coherently-unital-mul-H-Space pointed-Π-H-Space

  coherent-unital-mul-pointed-Π-H-Space :
    coherent-unital-mul-Pointed-Type pointed-type-pointed-Π-H-Space
  coherent-unital-mul-pointed-Π-H-Space =
    coherent-unital-mul-H-Space pointed-Π-H-Space

  magma-pointed-Π-H-Space : Magma (l1 ⊔ l2)
  magma-pointed-Π-H-Space = magma-H-Space pointed-Π-H-Space
```

## See also

- Pointed dependent function H-spaces are a special case of
  [dependent extension H-spaces](structured-types.dependent-extension-h-spaces.md)
