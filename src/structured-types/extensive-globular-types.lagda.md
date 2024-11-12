# Extensive globular types

```agda
{-# OPTIONS --guardedness #-}

module structured-types.extensive-globular-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import structured-types.reflexive-globular-types
```

**Disclaimer.** The contents of this file are experimental, and likely to be changed or reconsidered.

## Idea

An {{#concept "extensive globular type" Agda=Extensive-Globular-Type}} is a [reflexive globular type](structured-types.reflexive-globular-types.md) `G` such that the binary family of globular types

```text
  G' : G₀ → G₀ → Globular-Type
```

of 1-cells and higher cells [extends pointwise](structured-types.pointwise-extensions-binary-families-globular-types.md) to a [binary dependent globular type](structured-types.binary-dependent-globular-types.md). More specifically, an extensive globular type consists of a reflexive globular type `G` equipped with a binary dependent globular type

```text
  H : Binary-Dependent-Globular-Type l2 l2 G G
```

and a family of [globular equivalences](structured-types.globular-equivalences.md)

```text
  (x y : G₀) → ev-point H x y ≃ G' x y.
```

The low-dimensional data of an extensive globular type is therefore as follows:

```text
  G₀ : Type

  G₁ : (x y : G₀) → Type
  H₀ : (x y : G₀) → Type
  e₀ : {x y : G₀} → H₀ x y ≃ G₀ x y

  G₂ : {x y : G₀} (s t : G₁ x y) → Type
  H₁ : {x x' y y' : G₀} → G₁ x x' → G₁ y y' → H₀ x y → H₀ x' y' → Type
  e₁ : {x y : G₀} {s t : H₀ x y} → H₁ (Gᵣ x) (Gᵣ y) s t ≃ G₂ (e₀ s) (e₀ t)

  G₃ : {x y : G₀} {s t : G₁ x y} (u v : G₂ s t) → Type
  H₂ : {x x' y y' : G₀} {s s' : G₁ x x'} {t t' : G₁ y y'}
       (p : G₂ s s') (q : G₂ t t') → H₁ s t → H₁ s' t' → Type
  e₂ : {x y : G₀} {s t : G₁ x y} {u v : H₁ s t} →
       H₂ (Gᵣ s) (Gᵣ t) u v ≃ G₃ (e₁
```

## Definitions

### The predicate of being an extensive globular type

```agda
is-extensive-Globular-Type :
  {l1 l2 : Level} (G : Reflexive-Globular-Type l1 l2) → UU {!!}
is-extensive-Globular-Type =
  {!pointwise-!}
```

### Extensive globular types
