# Conjugation of pointed types

```agda
module structured-types.conjugation-pointed-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import structured-types.pointed-homotopies
open import structured-types.pointed-maps
open import structured-types.pointed-types

open import synthetic-homotopy-theory.conjugation-loops
open import synthetic-homotopy-theory.functoriality-loop-spaces
open import synthetic-homotopy-theory.loop-spaces
```

</details>

## Idea

{{#concept "Conjugation" Agda=conjugation-Pointed-Type}} on a
[pointed type](structured-types.pointed-types.md) `(B,b)` is defined as a family
of [pointed maps](structured-types.pointed-maps.md) `conj u p : (B,b) →∗ (B,u)`
indexed by `u : B` and `p : b ＝ u`, such that `conj b ω` acts on the
[loop space](synthetic-homotopy-theory.loop-spaces.md) `Ω (B , b)` by
conjugation, i.e., it maps a loop `α : b ＝ b` to the loop `ω⁻¹αω`.

## Definition

```agda
module _
  {l : Level} (B : Pointed-Type l)
  where

  map-conjugation-Pointed-Type :
    {u : type-Pointed-Type B} (p : point-Pointed-Type B ＝ u) →
    type-Pointed-Type B → type-Pointed-Type B
  map-conjugation-Pointed-Type refl = id

  preserves-point-conjugation-Pointed-Type :
    {u : type-Pointed-Type B} (p : point-Pointed-Type B ＝ u) →
    map-conjugation-Pointed-Type p (point-Pointed-Type B) ＝ u
  preserves-point-conjugation-Pointed-Type refl = refl

  conjugation-Pointed-Type :
    {u : type-Pointed-Type B} (p : point-Pointed-Type B ＝ u) →
    B →∗ (type-Pointed-Type B , u)
  pr1 (conjugation-Pointed-Type p) = map-conjugation-Pointed-Type p
  pr2 (conjugation-Pointed-Type p) = preserves-point-conjugation-Pointed-Type p
```

## Properties

### The conjugation map on a pointed type acts on loop spaces by conjugation

```agda
module _
  {l : Level} {B : Pointed-Type l}
  where

  action-on-loops-conjugation-Pointed-Type :
    {u : type-Pointed-Type B} (p : point-Pointed-Type B ＝ u) →
    Ω B →∗ Ω (type-Pointed-Type B , u)
  action-on-loops-conjugation-Pointed-Type p =
    pointed-map-Ω (conjugation-Pointed-Type B p)

  map-action-on-loops-conjugation-Pointed-Type :
    {u : type-Pointed-Type B} (p : point-Pointed-Type B ＝ u) →
    type-Ω B → type-Ω (type-Pointed-Type B , u)
  map-action-on-loops-conjugation-Pointed-Type p =
    map-pointed-map
      ( action-on-loops-conjugation-Pointed-Type p)

  preserves-point-action-on-loops-conjugation-Pointed-Type :
    {u : type-Pointed-Type B} (p : point-Pointed-Type B ＝ u) →
    map-action-on-loops-conjugation-Pointed-Type p refl ＝ refl
  preserves-point-action-on-loops-conjugation-Pointed-Type p =
    preserves-point-pointed-map
      ( action-on-loops-conjugation-Pointed-Type p)

  compute-action-on-loops-conjugation-Pointed-Type' :
    {u : type-Pointed-Type B} (p : point-Pointed-Type B ＝ u) →
    conjugation-Ω' p ~∗ action-on-loops-conjugation-Pointed-Type p
  pr1 (compute-action-on-loops-conjugation-Pointed-Type' refl) ω = inv (ap-id ω)
  pr2 (compute-action-on-loops-conjugation-Pointed-Type' refl) = refl

  compute-action-on-loops-conjugation-Pointed-Type :
    {u : type-Pointed-Type B} (p : point-Pointed-Type B ＝ u) →
    conjugation-Ω p ~∗ action-on-loops-conjugation-Pointed-Type p
  compute-action-on-loops-conjugation-Pointed-Type p =
    concat-pointed-htpy
      ( compute-conjugation-Ω p)
      ( compute-action-on-loops-conjugation-Pointed-Type' p)

  htpy-compute-action-on-loops-conjugation-Pointed-Type :
    {u : type-Pointed-Type B} (p : point-Pointed-Type B ＝ u) →
    map-conjugation-Ω p ~ map-action-on-loops-conjugation-Pointed-Type p
  htpy-compute-action-on-loops-conjugation-Pointed-Type p =
    pr1 (compute-action-on-loops-conjugation-Pointed-Type p)
```
