# Conjugation of loops

```agda
module synthetic-homotopy-theory.conjugation-loops where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import structured-types.pointed-equivalences
open import structured-types.pointed-homotopies
open import structured-types.pointed-maps

open import synthetic-homotopy-theory.loop-spaces
```

</details>

## Idea

For any [identification](foundation.identity-types.md) `p : x ＝ y` in a type
`A` there is a
{{#concept "conjugation action" Disambiguation="pointed map, on loop spaces of pointed types" Agda=conjugation-Ω}}
`Ω (A , x) →∗ Ω (A , y)` on
[loop spaces](synthetic-homotopy-theory.loop-spaces.md), which is the
[pointed map](structured-types.pointed-maps.md) given by `ω ↦ p⁻¹ωp`.

## Definition

### The standard definition of conjugation on loop spaces

```agda
module _
  {l : Level} {A : UU l}
  where

  conjugation-type-Ω : {x y : A} (p : x ＝ y) → type-Ω (A , x) → type-Ω (A , y)
  conjugation-type-Ω p ω = inv p ∙ (ω ∙ p)

  preserves-point-conjugation-Ω :
    {x y : A} (p : x ＝ y) → conjugation-type-Ω p refl ＝ refl
  preserves-point-conjugation-Ω p = left-inv p

  conjugation-Ω : {x y : A} (p : x ＝ y) → Ω (A , x) →∗ Ω (A , y)
  pr1 (conjugation-Ω p) = conjugation-type-Ω p
  pr2 (conjugation-Ω p) = preserves-point-conjugation-Ω p
```

## Properties

### Conjugation is a pointed equivalence

```agda
module _
  {l : Level} {A : UU l}
  where

  is-equiv-conjugation-type-Ω :
    {x y : A} (p : x ＝ y) → is-equiv (conjugation-type-Ω p)
  is-equiv-conjugation-type-Ω {x} {y} p =
    is-equiv-comp
      ( concat (inv p) y)
      ( concat' x p)
      ( is-equiv-concat' x p)
      ( is-equiv-concat (inv p) y)

  equiv-conjugation-type-Ω :
    {x y : A} (p : x ＝ y) → type-Ω (A , x) ≃ type-Ω (A , y)
  equiv-conjugation-type-Ω p =
    ( conjugation-type-Ω p , is-equiv-conjugation-type-Ω p)

  equiv-conjugation-Ω :
    {x y : A} (p : x ＝ y) → Ω (A , x) ≃∗ Ω (A , y)
  equiv-conjugation-Ω p =
    ( equiv-conjugation-type-Ω p , preserves-point-conjugation-Ω p)
```

### Conjugation on loop spaces is homotopic to transport

```agda
module _
  {l : Level} {A : UU l}
  where

  htpy-compute-conjugation-Ω :
    {x y : A} (p : x ＝ y) → conjugation-type-Ω p ~ tr-type-Ω p
  htpy-compute-conjugation-Ω refl ω = right-unit

  coherence-point-compute-conjugation-Ω :
    {x y : A} (p : x ＝ y) →
    coherence-point-unpointed-htpy-pointed-Π
      ( conjugation-Ω p)
      ( tr-Ω p)
      ( htpy-compute-conjugation-Ω p)
  coherence-point-compute-conjugation-Ω refl = refl

  compute-conjugation-Ω :
    {x y : A} (p : x ＝ y) → conjugation-Ω p ~∗ tr-Ω p
  pr1 (compute-conjugation-Ω p) = htpy-compute-conjugation-Ω p
  pr2 (compute-conjugation-Ω p) = coherence-point-compute-conjugation-Ω p
```
