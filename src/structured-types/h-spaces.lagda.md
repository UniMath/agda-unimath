# H-spaces

```agda
module structured-types.h-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.evaluation-functions
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.sections
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.unital-binary-operations
open import foundation.universe-levels
open import foundation.whiskering-identifications-concatenation

open import foundation-core.endomorphisms

open import structured-types.magmas
open import structured-types.noncoherent-h-spaces
open import structured-types.pointed-homotopies
open import structured-types.pointed-maps
open import structured-types.pointed-sections
open import structured-types.pointed-types
```

</details>

## Idea

A (coherent) {{#concept "H-space" WD="H-space" WDID=Q1562471 Agda=H-Space}} is a
"wild unital magma", i.e., it is a
[pointed type](structured-types.pointed-types.md)
[equipped](foundation.structure.md) with a binary operation for which the base
point is a unit, with a coherence law between the left and the right unit laws.

## Definitions

### Unital binary operations on pointed types

```agda
coherent-unit-laws-mul-Pointed-Type :
  {l : Level} (A : Pointed-Type l)
  (μ : (x y : type-Pointed-Type A) → type-Pointed-Type A) → UU l
coherent-unit-laws-mul-Pointed-Type A μ =
  coherent-unit-laws μ (point-Pointed-Type A)

coherent-unital-mul-Pointed-Type :
  {l : Level} → Pointed-Type l → UU l
coherent-unital-mul-Pointed-Type A =
  Σ ( type-Pointed-Type A → type-Pointed-Type A → type-Pointed-Type A)
    ( coherent-unit-laws-mul-Pointed-Type A)
```

### H-spaces

An H-space consists of a pointed type `X` and a coherent unital multiplication
on `X`. The entry `make-H-Space` is provided to break up the construction of an
H-space into two components: the construction of its underlying pointed type and
the construction of the coherently unital multiplication on this pointed type.
Furthermore, this definition suggests that any construction of an H-space should
be refactored by first defining its underlying pointed type, then defining its
coherently unital multiplication, and finally combining those two constructions
using `make-H-Space`.

```agda
H-Space : (l : Level) → UU (lsuc l)
H-Space l =
  Σ (Pointed-Type l) coherent-unital-mul-Pointed-Type

make-H-Space :
  {l : Level} →
  (X : Pointed-Type l) → coherent-unital-mul-Pointed-Type X → H-Space l
make-H-Space X μ = (X , μ)

{-# INLINE make-H-Space #-}

module _
  {l : Level} (M : H-Space l)
  where

  pointed-type-H-Space : Pointed-Type l
  pointed-type-H-Space = pr1 M

  type-H-Space : UU l
  type-H-Space = type-Pointed-Type pointed-type-H-Space

  unit-H-Space : type-H-Space
  unit-H-Space = point-Pointed-Type pointed-type-H-Space

  coherent-unital-mul-H-Space :
    coherent-unital-mul-Pointed-Type pointed-type-H-Space
  coherent-unital-mul-H-Space = pr2 M

  mul-H-Space :
    type-H-Space → type-H-Space → type-H-Space
  mul-H-Space = pr1 coherent-unital-mul-H-Space

  mul-H-Space' :
    type-H-Space → type-H-Space → type-H-Space
  mul-H-Space' x y = mul-H-Space y x

  ap-mul-H-Space :
    {a b c d : type-H-Space} → a ＝ b → c ＝ d →
    mul-H-Space a c ＝ mul-H-Space b d
  ap-mul-H-Space p q = ap-binary mul-H-Space p q

  magma-H-Space : Magma l
  pr1 magma-H-Space = type-H-Space
  pr2 magma-H-Space = mul-H-Space

  coherent-unit-laws-mul-H-Space :
    coherent-unit-laws mul-H-Space unit-H-Space
  coherent-unit-laws-mul-H-Space =
    pr2 coherent-unital-mul-H-Space

  left-unit-law-mul-H-Space :
    (x : type-H-Space) →
    mul-H-Space unit-H-Space x ＝ x
  left-unit-law-mul-H-Space =
    pr1 coherent-unit-laws-mul-H-Space

  right-unit-law-mul-H-Space :
    (x : type-H-Space) →
    mul-H-Space x unit-H-Space ＝ x
  right-unit-law-mul-H-Space =
    pr1 (pr2 coherent-unit-laws-mul-H-Space)

  coh-unit-laws-mul-H-Space :
    left-unit-law-mul-H-Space unit-H-Space ＝
    right-unit-law-mul-H-Space unit-H-Space
  coh-unit-laws-mul-H-Space =
    pr2 (pr2 coherent-unit-laws-mul-H-Space)

  unit-laws-mul-H-Space :
    unit-laws mul-H-Space unit-H-Space
  pr1 unit-laws-mul-H-Space = left-unit-law-mul-H-Space
  pr2 unit-laws-mul-H-Space = right-unit-law-mul-H-Space

  is-unital-mul-H-Space : is-unital mul-H-Space
  pr1 is-unital-mul-H-Space = unit-H-Space
  pr2 is-unital-mul-H-Space = unit-laws-mul-H-Space

  is-coherently-unital-mul-H-Space :
    is-coherently-unital mul-H-Space
  pr1 is-coherently-unital-mul-H-Space = unit-H-Space
  pr2 is-coherently-unital-mul-H-Space =
    coherent-unit-laws-mul-H-Space
```

## Properties

### Every noncoherent H-space can be upgraded to a coherent H-space

```agda
h-space-Noncoherent-H-Space :
  {l : Level} → Noncoherent-H-Space l → H-Space l
pr1 (h-space-Noncoherent-H-Space A) =
  pointed-type-Noncoherent-H-Space A
pr1 (pr2 (h-space-Noncoherent-H-Space A)) =
  mul-Noncoherent-H-Space A
pr2 (pr2 (h-space-Noncoherent-H-Space A)) =
  coherent-unit-laws-unit-laws
    ( mul-Noncoherent-H-Space A)
    ( unit-laws-mul-Noncoherent-H-Space A)
```

### The type of H-space structures on `A` is equivalent to the type of sections of `ev-point : (A → A, id) →∗ A`

This is Proposition 2.2 (1)⇔(2) {{#cite BCFR23}}.

```agda
module _
  {l : Level} (A : Pointed-Type l)
  where

  ev-endo-Pointed-Type : endo-Pointed-Type (type-Pointed-Type A) →∗ A
  pr1 ev-endo-Pointed-Type = ev-point-Pointed-Type A
  pr2 ev-endo-Pointed-Type = refl

  pointed-section-ev-point-Pointed-Type : UU l
  pointed-section-ev-point-Pointed-Type =
    pointed-section ev-endo-Pointed-Type

  compute-pointed-section-ev-point-Pointed-Type :
    pointed-section-ev-point-Pointed-Type ≃ coherent-unital-mul-Pointed-Type A
  compute-pointed-section-ev-point-Pointed-Type =
    ( equiv-tot
      ( λ x →
        equiv-Σ
          ( λ α →
            Σ ( right-unit-law x (point-Pointed-Type A))
              ( coh-unit-laws x (point-Pointed-Type A) α))
          ( equiv-funext)
          ( λ _ → equiv-tot (λ _ → equiv-right-unwhisker-concat refl)))) ∘e
    ( associative-Σ)

module _
  {l : Level} (A : H-Space l)
  where

  ev-endo-H-Space :
    endo-Pointed-Type (type-H-Space A) →∗ pointed-type-H-Space A
  ev-endo-H-Space = ev-endo-Pointed-Type (pointed-type-H-Space A)

  pointed-section-ev-endo-H-Space : pointed-section ev-endo-H-Space
  pointed-section-ev-endo-H-Space =
    map-inv-equiv
      ( compute-pointed-section-ev-point-Pointed-Type (pointed-type-H-Space A))
      ( coherent-unital-mul-H-Space A)

  section-ev-endo-H-Space : section (map-pointed-map ev-endo-H-Space)
  section-ev-endo-H-Space =
    section-pointed-section ev-endo-H-Space pointed-section-ev-endo-H-Space
```

## References

{{#bibliography}}
