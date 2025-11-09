# Extension H-spaces

```agda
module structured-types.extension-h-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-types
open import foundation.unital-binary-operations
open import foundation.universe-levels

open import structured-types.dependent-extension-h-spaces
open import structured-types.h-spaces
open import structured-types.magmas
open import structured-types.pointed-types
```

</details>

## Idea

Given a map `h : A → B` and an [H-space](structured-types.h-spaces.md) `M`, the
{{#concept "extension H-space" Agda=extension-H-Space}} `extension h M` is an
H-space consisting of
[extensions](orthogonal-factorization-systems.extensions-maps.md) of the
constant family of units `η : A → M` in `M` along `h`. I.e., maps `f : B → M`
[equipped](foundation.structure.md) with a
[homotopy](foundation-core.homotopies.md) `f ∘ h ~ η`. The multiplication is
given pointwise, and on the homotopy by the
[binary action on identifications](foundation.action-on-identifications-binary-functions.md)
of the multiplication operation of `M`.

## Definition

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (h : A → B) (M : H-Space l3)
  where

  extension-H-Space : H-Space (l1 ⊔ l2 ⊔ l3)
  extension-H-Space = extension-Π-H-Space h (λ _ → M)

  pointed-type-extension-H-Space : Pointed-Type (l1 ⊔ l2 ⊔ l3)
  pointed-type-extension-H-Space =
    pointed-type-H-Space extension-H-Space

  type-extension-H-Space : UU (l1 ⊔ l2 ⊔ l3)
  type-extension-H-Space =
    type-H-Space extension-H-Space

  unit-extension-H-Space : type-extension-H-Space
  unit-extension-H-Space =
    unit-H-Space extension-H-Space

  mul-extension-H-Space :
    type-extension-H-Space →
    type-extension-H-Space →
    type-extension-H-Space
  mul-extension-H-Space = mul-H-Space extension-H-Space

  left-unit-law-mul-extension-H-Space :
    (f : type-extension-H-Space) →
    mul-extension-H-Space unit-extension-H-Space f ＝ f
  left-unit-law-mul-extension-H-Space =
    left-unit-law-mul-H-Space extension-H-Space

  right-unit-law-mul-extension-H-Space :
    (f : type-extension-H-Space) →
    mul-extension-H-Space f unit-extension-H-Space ＝ f
  right-unit-law-mul-extension-H-Space =
    right-unit-law-mul-H-Space extension-H-Space

  is-unital-mul-extension-H-Space :
    is-unital mul-extension-H-Space
  is-unital-mul-extension-H-Space =
    is-unital-mul-H-Space extension-H-Space

  coh-unit-laws-mul-extension-H-Space :
    coh-unit-laws
      ( mul-extension-H-Space)
      ( unit-extension-H-Space)
      ( left-unit-law-mul-extension-H-Space)
      ( right-unit-law-mul-extension-H-Space)
  coh-unit-laws-mul-extension-H-Space =
    coh-unit-laws-mul-H-Space extension-H-Space

  coherent-unit-laws-mul-extension-H-Space :
    coherent-unit-laws mul-extension-H-Space unit-extension-H-Space
  coherent-unit-laws-mul-extension-H-Space =
    coherent-unit-laws-mul-H-Space extension-H-Space

  is-coherently-unital-mul-extension-H-Space :
    is-coherently-unital mul-extension-H-Space
  is-coherently-unital-mul-extension-H-Space =
    is-coherently-unital-mul-H-Space extension-H-Space

  coherent-unital-mul-extension-H-Space :
    coherent-unital-mul-Pointed-Type pointed-type-extension-H-Space
  coherent-unital-mul-extension-H-Space =
    coherent-unital-mul-H-Space extension-H-Space

  magma-extension-H-Space : Magma (l1 ⊔ l2 ⊔ l3)
  magma-extension-H-Space = magma-H-Space extension-H-Space
```
