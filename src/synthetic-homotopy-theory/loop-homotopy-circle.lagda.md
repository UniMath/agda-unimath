# The loop homotopy on the circle

```agda
module synthetic-homotopy-theory.loop-homotopy-circle where
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

The
{{#concept "loop homotopy" Disambiguation="on the circle type" Agda=loop-htpy-𝕊¹}}
on the [circle](synthetic-homotopy-theory.circle.md) is the family of
[equalities](foundation-core.identity-types.md)

```text
  loop-htpy-𝕊¹ : (x : 𝕊¹) → x ＝ x
```

defined by [transporting](foundation-core.transport-along-identifications.md)
along the loop of the circle. This [homotopy](foundation-core.homotopies.md) is
distinct from the constant homotopy and has winding number 1.

## Definitions

### The loop homotopy on the circle

```agda
loop-htpy-𝕊¹ : (x : 𝕊¹) → x ＝ x
loop-htpy-𝕊¹ =
  function-apply-dependent-universal-property-𝕊¹
    ( eq-value id id)
    ( loop-𝕊¹)
    ( map-compute-dependent-identification-eq-value-id-id
      ( loop-𝕊¹)
      ( loop-𝕊¹)
      ( loop-𝕊¹)
      ( refl))

compute-base-loop-htpy-𝕊¹ : loop-htpy-𝕊¹ base-𝕊¹ ＝ loop-𝕊¹
compute-base-loop-htpy-𝕊¹ =
  base-dependent-universal-property-𝕊¹
    ( eq-value id id)
    ( loop-𝕊¹)
    ( map-compute-dependent-identification-eq-value-id-id
      ( loop-𝕊¹)
      ( loop-𝕊¹)
      ( loop-𝕊¹)
      ( refl))
```

## Properties

### The loop homotopy on the circle is nontrivial

```agda
abstract
  is-not-refl-ev-base-loop-htpy-𝕊¹ : loop-htpy-𝕊¹ base-𝕊¹ ≠ refl
  is-not-refl-ev-base-loop-htpy-𝕊¹ p =
    is-nontrivial-loop-𝕊¹ (inv compute-base-loop-htpy-𝕊¹ ∙ p)

is-nontrivial-loop-htpy-𝕊¹' : ¬ (loop-htpy-𝕊¹ ~ refl-htpy)
is-nontrivial-loop-htpy-𝕊¹' H =
  is-not-refl-ev-base-loop-htpy-𝕊¹ (H base-𝕊¹)

is-nontrivial-loop-htpy-𝕊¹ : loop-htpy-𝕊¹ ≠ refl-htpy
is-nontrivial-loop-htpy-𝕊¹ =
  nonequal-Π loop-htpy-𝕊¹ refl-htpy base-𝕊¹ is-not-refl-ev-base-loop-htpy-𝕊¹
```
