# The multiplication operation on the circle

```agda
module synthetic-homotopy-theory.multiplication-circle where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import structured-types.pointed-homotopies
open import structured-types.pointed-maps

open import synthetic-homotopy-theory.circle
```

</details>

## Idea

Classically, the circle can be viewed as the subset of the complex numbers of
absolute value 1. The absolute value of a product of complex numbers is the
product of their absolute values. This implies that when we multiply two complex
numbers on the unit circle, the result is a complex number on the unit circle.
This multiplicative structure carries over to the homotopy type of the
[circle](synthetic-homotopy-theory.circle.md).

## Definition

### Homotopy `id ~ id` of degree one

```agda
htpy-id-id-Π-𝕊¹ :
  Π-𝕊¹
    ( eq-value id id)
    ( loop-𝕊¹)
    ( map-compute-dependent-identification-eq-value-id-id
      ( loop-𝕊¹)
      ( loop-𝕊¹)
      ( loop-𝕊¹)
      ( refl))
htpy-id-id-Π-𝕊¹ =
  apply-dependent-universal-property-𝕊¹
    ( eq-value id id)
    ( loop-𝕊¹)
    ( map-compute-dependent-identification-eq-value-id-id
      ( loop-𝕊¹)
      ( loop-𝕊¹)
      ( loop-𝕊¹)
      ( refl))

htpy-id-id-𝕊¹ : (x : 𝕊¹) → Id x x
htpy-id-id-𝕊¹ = pr1 htpy-id-id-Π-𝕊¹

htpy-id-id-base-𝕊¹ : Id (htpy-id-id-𝕊¹ base-𝕊¹) loop-𝕊¹
htpy-id-id-base-𝕊¹ = pr1 (pr2 htpy-id-id-Π-𝕊¹)
```

### Multiplication on the circle

```agda
Mul-Π-𝕊¹ : 𝕊¹ → UU lzero
Mul-Π-𝕊¹ x = 𝕊¹-Pointed-Type →∗ (pair 𝕊¹ x)

dependent-identification-Mul-Π-𝕊¹ :
  {x : 𝕊¹} (p : Id base-𝕊¹ x) (q : Mul-Π-𝕊¹ base-𝕊¹) (r : Mul-Π-𝕊¹ x) →
  (H : pr1 q ~ pr1 r) → Id (pr2 q ∙ p) (H base-𝕊¹ ∙ pr2 r) →
  Id (tr Mul-Π-𝕊¹ p q) r
dependent-identification-Mul-Π-𝕊¹ {x} refl q r H u =
  eq-pointed-htpy q r (H , inv right-unit ∙ u)

eq-id-id-𝕊¹-Pointed-Type :
  Id (tr Mul-Π-𝕊¹ loop-𝕊¹ id-pointed-map) id-pointed-map
eq-id-id-𝕊¹-Pointed-Type =
  dependent-identification-Mul-Π-𝕊¹ loop-𝕊¹
    ( id-pointed-map)
    ( id-pointed-map)
    ( htpy-id-id-𝕊¹)
    ( inv htpy-id-id-base-𝕊¹ ∙ inv right-unit)

mul-Π-𝕊¹ : Π-𝕊¹ (Mul-Π-𝕊¹) (id-pointed-map) (eq-id-id-𝕊¹-Pointed-Type)
mul-Π-𝕊¹ =
  apply-dependent-universal-property-𝕊¹
    ( Mul-Π-𝕊¹)
    ( id-pointed-map)
    ( eq-id-id-𝕊¹-Pointed-Type)

mul-𝕊¹ : 𝕊¹ → 𝕊¹ → 𝕊¹
mul-𝕊¹ x = pr1 (pr1 mul-Π-𝕊¹ x)

left-unit-law-mul-𝕊¹ : (x : 𝕊¹) → Id (mul-𝕊¹ base-𝕊¹ x) x
left-unit-law-mul-𝕊¹ = htpy-eq (ap pr1 (pr1 (pr2 mul-Π-𝕊¹)))

right-unit-law-mul-𝕊¹ : (x : 𝕊¹) → Id (mul-𝕊¹ x base-𝕊¹) x
right-unit-law-mul-𝕊¹ x = pr2 (pr1 mul-Π-𝕊¹ x)
```
