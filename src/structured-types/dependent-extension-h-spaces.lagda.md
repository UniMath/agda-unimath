# Dependent extension H-spaces

```agda
module structured-types.dependent-extension-h-spaces where
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

open import orthogonal-factorization-systems.equality-extensions-maps
open import orthogonal-factorization-systems.extensions-dependent-maps

open import structured-types.h-spaces
open import structured-types.magmas
open import structured-types.noncoherent-h-spaces
open import structured-types.pointed-dependent-functions
open import structured-types.pointed-homotopies
open import structured-types.pointed-types
```

</details>

## Idea

Given a map `h : A → B` and a family of [H-spaces](structured-types.h-spaces.md)
`M i` indexed by `B`, the
{{#concept "dependent extension H-space" Agda=extension-Π-H-Space}}
`extension-Π h M` is an H-space consisting of
[dependent extensions](orthogonal-factorization-systems.extensions-dependent-maps.md)
of the family of units `η : (i : A) → M (h i)` in `M` along `h`. I.e., maps
`f : (i : B) → M i` [equipped](foundation.structure.md) with a
[homotopy](foundation-core.homotopies.md) `f ∘ h ~ η`. The multiplication is
given pointwise, and on the homotopy by the
[binary action on identifications](foundation.action-on-identifications-binary-functions.md)
of the pointwise multiplication operation of `M`.

## Definition

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (h : A → B)
  (M : B → H-Space l3)
  where

  type-extension-Π-H-Space : UU (l1 ⊔ l2 ⊔ l3)
  type-extension-Π-H-Space =
    extension-dependent-type' h (type-H-Space ∘ M) (unit-H-Space ∘ M ∘ h)

  unit-extension-Π-H-Space : type-extension-Π-H-Space
  unit-extension-Π-H-Space = (unit-H-Space ∘ M , refl-htpy)

  pointed-type-extension-Π-H-Space : Pointed-Type (l1 ⊔ l2 ⊔ l3)
  pointed-type-extension-Π-H-Space =
    ( type-extension-Π-H-Space , unit-extension-Π-H-Space)

  mul-extension-Π-H-Space :
    type-extension-Π-H-Space →
    type-extension-Π-H-Space →
    type-extension-Π-H-Space
  pr1 (mul-extension-Π-H-Space (f , f∗) (g , g∗)) i =
    mul-H-Space (M i) (f i) (g i)
  pr2 (mul-extension-Π-H-Space (f , f∗) (g , g∗)) i =
    ( ap-binary (mul-H-Space (M (h i))) (f∗ i) (g∗ i)) ∙
    ( left-unit-law-mul-H-Space (M (h i)) (unit-H-Space (M (h i))))

  htpy-left-unit-law-mul-extension-Π-H-Space :
    (f : type-extension-Π-H-Space) →
    htpy-extension'
      ( h)
      ( unit-H-Space ∘ M ∘ h)
      ( mul-extension-Π-H-Space unit-extension-Π-H-Space f)
      ( f)
  pr1 (htpy-left-unit-law-mul-extension-Π-H-Space (f , f∗)) i =
    left-unit-law-mul-H-Space (M i) (f i)
  pr2 (htpy-left-unit-law-mul-extension-Π-H-Space (f , f∗)) i =
    inv-nat-htpy-id (left-unit-law-mul-H-Space (M (h i))) (f∗ i)

  left-unit-law-mul-extension-Π-H-Space :
    (f : type-extension-Π-H-Space) →
    mul-extension-Π-H-Space unit-extension-Π-H-Space f ＝ f
  left-unit-law-mul-extension-Π-H-Space f =
    eq-htpy-extension'
      ( h)
      ( unit-H-Space ∘ M ∘ h)
      ( mul-extension-Π-H-Space unit-extension-Π-H-Space f)
      ( f)
      ( htpy-left-unit-law-mul-extension-Π-H-Space f)

  htpy-right-unit-law-mul-extension-Π-H-Space' :
    (f : type-extension-Π-H-Space) →
    htpy-extension'
      ( h)
      ( unit-H-Space ∘ M ∘ h)
      ( mul-extension-Π-H-Space f unit-extension-Π-H-Space)
      ( f)
  pr1 (htpy-right-unit-law-mul-extension-Π-H-Space' (f , f∗)) i =
    right-unit-law-mul-H-Space (M i) (f i)
  pr2 (htpy-right-unit-law-mul-extension-Π-H-Space' (f , f∗)) i =
    equational-reasoning
      ( ( ap (λ f → mul-H-Space (M (h i)) f (unit-H-Space (M (h i)))) (f∗ i)) ∙
        ( refl)) ∙
      ( left-unit-law-mul-H-Space (M (h i)) (unit-H-Space (M (h i))))
      ＝
        ( ap (λ f → mul-H-Space (M (h i)) f (unit-H-Space (M (h i)))) (f∗ i)) ∙
        ( right-unit-law-mul-H-Space (M (h i)) (unit-H-Space (M (h i))))
        by ap-binary (_∙_) right-unit (coh-unit-laws-mul-H-Space (M (h i)))
      ＝
        ( right-unit-law-mul-H-Space (M (h i)) (f (h i)) ∙ f∗ i)
        by inv-nat-htpy-id (right-unit-law-mul-H-Space (M (h i))) (f∗ i)

  right-unit-law-mul-extension-Π-H-Space' :
    (f : type-extension-Π-H-Space) →
    mul-extension-Π-H-Space f unit-extension-Π-H-Space ＝ f
  right-unit-law-mul-extension-Π-H-Space' f =
    eq-htpy-extension'
      ( h)
      ( unit-H-Space ∘ M ∘ h)
      ( mul-extension-Π-H-Space f unit-extension-Π-H-Space)
      ( f)
      ( htpy-right-unit-law-mul-extension-Π-H-Space' f)

  noncoherent-h-space-extension-Π-H-Space : Noncoherent-H-Space (l1 ⊔ l2 ⊔ l3)
  noncoherent-h-space-extension-Π-H-Space =
    ( pointed-type-extension-Π-H-Space ,
      mul-extension-Π-H-Space ,
      left-unit-law-mul-extension-Π-H-Space ,
      right-unit-law-mul-extension-Π-H-Space')

  extension-Π-H-Space : H-Space (l1 ⊔ l2 ⊔ l3)
  extension-Π-H-Space =
    h-space-Noncoherent-H-Space noncoherent-h-space-extension-Π-H-Space

  right-unit-law-mul-extension-Π-H-Space :
    (f : type-extension-Π-H-Space) →
    mul-extension-Π-H-Space f unit-extension-Π-H-Space ＝ f
  right-unit-law-mul-extension-Π-H-Space =
    right-unit-law-mul-H-Space extension-Π-H-Space

  is-unital-mul-extension-Π-H-Space : is-unital mul-extension-Π-H-Space
  is-unital-mul-extension-Π-H-Space = is-unital-mul-H-Space extension-Π-H-Space

  coh-unit-laws-mul-extension-Π-H-Space :
    coh-unit-laws
      ( mul-extension-Π-H-Space)
      ( unit-extension-Π-H-Space)
      ( left-unit-law-mul-extension-Π-H-Space)
      ( right-unit-law-mul-extension-Π-H-Space)
  coh-unit-laws-mul-extension-Π-H-Space =
    coh-unit-laws-mul-H-Space extension-Π-H-Space

  coherent-unit-laws-mul-extension-Π-H-Space :
    coherent-unit-laws mul-extension-Π-H-Space unit-extension-Π-H-Space
  coherent-unit-laws-mul-extension-Π-H-Space =
    coherent-unit-laws-mul-H-Space extension-Π-H-Space

  is-coherently-unital-mul-extension-Π-H-Space :
    is-coherently-unital mul-extension-Π-H-Space
  is-coherently-unital-mul-extension-Π-H-Space =
    is-coherently-unital-mul-H-Space extension-Π-H-Space

  coherent-unital-mul-extension-Π-H-Space :
    coherent-unital-mul-Pointed-Type pointed-type-extension-Π-H-Space
  coherent-unital-mul-extension-Π-H-Space =
    coherent-unital-mul-H-Space extension-Π-H-Space

  magma-extension-Π-H-Space : Magma (l1 ⊔ l2 ⊔ l3)
  magma-extension-Π-H-Space = magma-H-Space extension-Π-H-Space
```
