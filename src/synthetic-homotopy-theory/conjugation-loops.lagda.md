# Conjugation of loops

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module synthetic-homotopy-theory.conjugation-loops
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.homotopies funext
open import foundation.identity-types funext
open import foundation.universe-levels

open import structured-types.pointed-homotopies funext univalence truncations
open import structured-types.pointed-maps funext univalence truncations

open import synthetic-homotopy-theory.loop-spaces funext univalence truncations
```

</details>

## Idea

For any [identification](foundation.identity-types.md) `p : x ＝ y` in a type
`A` there is an **conjugation action** `Ω (A , x) →∗ Ω (A , y)` on
[loop spaces](synthetic-homotopy-theory.loop-spaces.md), which is the
[pointed map](structured-types.pointed-maps.md) given by `ω ↦ p⁻¹ωp`.

## Definition

### The standard definition of conjugation on loop spaces

```agda
module _
  {l : Level} {A : UU l}
  where

  map-conjugation-Ω : {x y : A} (p : x ＝ y) → type-Ω (A , x) → type-Ω (A , y)
  map-conjugation-Ω p ω = inv p ∙ (ω ∙ p)

  preserves-point-conjugation-Ω :
    {x y : A} (p : x ＝ y) → map-conjugation-Ω p refl ＝ refl
  preserves-point-conjugation-Ω p = left-inv p

  conjugation-Ω : {x y : A} (p : x ＝ y) → Ω (A , x) →∗ Ω (A , y)
  pr1 (conjugation-Ω p) = map-conjugation-Ω p
  pr2 (conjugation-Ω p) = preserves-point-conjugation-Ω p
```

### A second definition of conjugation on loop spaces

```agda
module _
  {l : Level} {A : UU l}
  where

  conjugation-Ω' : {x y : A} (p : x ＝ y) → Ω (A , x) →∗ Ω (A , y)
  conjugation-Ω' refl = id-pointed-map

  map-conjugation-Ω' : {x y : A} (p : x ＝ y) → type-Ω (A , x) → type-Ω (A , y)
  map-conjugation-Ω' p = map-pointed-map (conjugation-Ω' p)

  preserves-point-conjugation-Ω' :
    {x y : A} (p : x ＝ y) → map-conjugation-Ω' p refl ＝ refl
  preserves-point-conjugation-Ω' p =
    preserves-point-pointed-map (conjugation-Ω' p)
```

## Properties

### The two definitions of conjugation on loop spaces are pointed homotopic

```agda
module _
  {l : Level} {A : UU l}
  where

  htpy-compute-conjugation-Ω :
    {x y : A} (p : x ＝ y) → map-conjugation-Ω p ~ map-conjugation-Ω' p
  htpy-compute-conjugation-Ω refl ω = right-unit

  coherence-point-compute-conjugation-Ω :
    {x y : A} (p : x ＝ y) →
    coherence-point-unpointed-htpy-pointed-Π
      ( conjugation-Ω p)
      ( conjugation-Ω' p)
      ( htpy-compute-conjugation-Ω p)
  coherence-point-compute-conjugation-Ω refl = refl

  compute-conjugation-Ω :
    {x y : A} (p : x ＝ y) → conjugation-Ω p ~∗ conjugation-Ω' p
  pr1 (compute-conjugation-Ω p) = htpy-compute-conjugation-Ω p
  pr2 (compute-conjugation-Ω p) = coherence-point-compute-conjugation-Ω p
```
