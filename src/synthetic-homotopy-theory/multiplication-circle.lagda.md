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
open import foundation.negated-equality
open import foundation.negation
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

## Definitions

### The degree 1 reflexivity homotopy on the circle

```agda
degree-1-refl-htpy-𝕊¹ : (x : 𝕊¹) → x ＝ x
degree-1-refl-htpy-𝕊¹ =
  function-apply-dependent-universal-property-𝕊¹
    ( eq-value id id)
    ( loop-𝕊¹)
    ( map-compute-dependent-identification-eq-value-id-id
      ( loop-𝕊¹)
      ( loop-𝕊¹)
      ( loop-𝕊¹)
      ( refl))

compute-base-degree-1-refl-htpy-𝕊¹ : degree-1-refl-htpy-𝕊¹ base-𝕊¹ ＝ loop-𝕊¹
compute-base-degree-1-refl-htpy-𝕊¹ =
  base-dependent-universal-property-𝕊¹
    ( eq-value id id)
    ( loop-𝕊¹)
    ( map-compute-dependent-identification-eq-value-id-id
      ( loop-𝕊¹)
      ( loop-𝕊¹)
      ( loop-𝕊¹)
      ( refl))
```

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
    ( degree-1-refl-htpy-𝕊¹)
    ( inv compute-base-degree-1-refl-htpy-𝕊¹ ∙ inv right-unit)

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

### The degree 1 reflexivity homotopy on the circle is nontrivial

```agda
abstract
  is-not-refl-ev-base-degree-1-refl-htpy-𝕊¹ :
    degree-1-refl-htpy-𝕊¹ base-𝕊¹ ≠ refl
  is-not-refl-ev-base-degree-1-refl-htpy-𝕊¹ p =
    is-nontrivial-loop-𝕊¹ (inv (compute-base-degree-1-refl-htpy-𝕊¹) ∙ p)

is-nontrivial-degree-1-refl-htpy-𝕊¹' : ¬ (degree-1-refl-htpy-𝕊¹ ~ refl-htpy)
is-nontrivial-degree-1-refl-htpy-𝕊¹' H =
  is-not-refl-ev-base-degree-1-refl-htpy-𝕊¹ (H base-𝕊¹)

is-nontrivial-degree-1-refl-htpy-𝕊¹ : degree-1-refl-htpy-𝕊¹ ≠ refl-htpy
is-nontrivial-degree-1-refl-htpy-𝕊¹ =
  nonequal-Π
    ( degree-1-refl-htpy-𝕊¹)
    ( refl-htpy)
    ( base-𝕊¹)
    ( is-not-refl-ev-base-degree-1-refl-htpy-𝕊¹)
```

### The unit laws of multiplication on the circle

```agda
left-unit-law-mul-𝕊¹ : (x : 𝕊¹) → mul-𝕊¹ base-𝕊¹ x ＝ x
left-unit-law-mul-𝕊¹ = htpy-eq (ap pr1 (pr1 (pr2 mul-Π-𝕊¹)))

right-unit-law-mul-𝕊¹ : (x : 𝕊¹) → mul-𝕊¹ x base-𝕊¹ ＝ x
right-unit-law-mul-𝕊¹ x = pr2 (pr1 mul-Π-𝕊¹ x)
```
