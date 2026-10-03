# The multiplication operation on the circle

```agda
module synthetic-homotopy-theory.multiplication-circle where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equality-fibers-of-maps
open import foundation.function-extensionality-axiom
open import foundation.homotopies
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import foundation-core.equality-dependent-pair-types

open import structured-types.h-spaces
open import structured-types.pointed-homotopies
open import structured-types.pointed-maps

open import synthetic-homotopy-theory.circle
open import synthetic-homotopy-theory.loop-homotopy-circle
```

</details>

## Idea

Classically, the circle can be viewed as the subset of the complex numbers of
absolute value 1. The absolute value of a product of complex numbers is the
product of their absolute values. This implies that when we multiply two complex
numbers on the unit circle, the result is a complex number on the unit circle.
This multiplicative structure carries over to the homotopy type of the
[circle](synthetic-homotopy-theory.circle.md). This multiplication gives the
circle the structure of an [H-space](structured-types.h-spaces.md).

## Definitions

### Multiplication on the circle

```agda
Mul-Π-𝕊¹ : 𝕊¹ → UU lzero
Mul-Π-𝕊¹ x = 𝕊¹-Pointed-Type →∗ (𝕊¹ , x)

dependent-identification-Mul-Π-𝕊¹ :
  {x : 𝕊¹} (p : base-𝕊¹ ＝ x) (q : Mul-Π-𝕊¹ base-𝕊¹) (r : Mul-Π-𝕊¹ x) →
  (H : pr1 q ~ pr1 r) →
  pr2 q ∙ p ＝ H base-𝕊¹ ∙ pr2 r →
  tr Mul-Π-𝕊¹ p q ＝ r
dependent-identification-Mul-Π-𝕊¹ refl q r H u =
  eq-pointed-htpy q r (H , inv right-unit ∙ u)

eq-id-id-𝕊¹-Pointed-Type :
  tr Mul-Π-𝕊¹ loop-𝕊¹ id-pointed-map ＝ id-pointed-map
eq-id-id-𝕊¹-Pointed-Type =
  dependent-identification-Mul-Π-𝕊¹ loop-𝕊¹
    ( id-pointed-map)
    ( id-pointed-map)
    ( loop-htpy-𝕊¹)
    ( inv compute-base-loop-htpy-𝕊¹ ∙ inv right-unit)

mul-Π-𝕊¹ : Π-𝕊¹ (Mul-Π-𝕊¹) (id-pointed-map) (eq-id-id-𝕊¹-Pointed-Type)
mul-Π-𝕊¹ =
  apply-dependent-universal-property-𝕊¹
    ( Mul-Π-𝕊¹)
    ( id-pointed-map)
    ( eq-id-id-𝕊¹-Pointed-Type)

mul-𝕊¹ : 𝕊¹ → 𝕊¹ → 𝕊¹
mul-𝕊¹ x = pr1 (pr1 mul-Π-𝕊¹ x)
```

## Properties

### The unit laws of multiplication on the circle

```agda
left-unit-law-mul-𝕊¹ : (x : 𝕊¹) → mul-𝕊¹ base-𝕊¹ x ＝ x
left-unit-law-mul-𝕊¹ = htpy-eq (ap pr1 (pr1 (pr2 mul-Π-𝕊¹)))

right-unit-law-mul-𝕊¹ : (x : 𝕊¹) → mul-𝕊¹ x base-𝕊¹ ＝ x
right-unit-law-mul-𝕊¹ x = pr2 (pr1 mul-Π-𝕊¹ x)
```

### The coherence between the unit laws

```agda
coh-unit-laws-mul-𝕊¹ :
  left-unit-law-mul-𝕊¹ base-𝕊¹ ＝ right-unit-law-mul-𝕊¹ base-𝕊¹
coh-unit-laws-mul-𝕊¹ =
  ( fiber-ap-eq-fiber-fiberwise
    ( λ f → f base-𝕊¹)
    ( pr1 mul-Π-𝕊¹ base-𝕊¹)
    ( id-pointed-map)
    ( ap pr1 (pr1 (pr2 mul-Π-𝕊¹)))
    ( dependent-identification-eq-pair (pr1 (pr2 mul-Π-𝕊¹)))) ∙
  right-unit
```

### The circle as an H-space

```agda
coherent-unital-mul-𝕊¹-Pointed-Type :
  coherent-unital-mul-Pointed-Type 𝕊¹-Pointed-Type
pr1 coherent-unital-mul-𝕊¹-Pointed-Type =
  mul-𝕊¹
pr2 coherent-unital-mul-𝕊¹-Pointed-Type =
  ( left-unit-law-mul-𝕊¹ , right-unit-law-mul-𝕊¹ , coh-unit-laws-mul-𝕊¹)

𝕊¹-H-Space : H-Space lzero
𝕊¹-H-Space =
  make-H-Space
    ( 𝕊¹-Pointed-Type)
    ( coherent-unital-mul-𝕊¹-Pointed-Type)
```
