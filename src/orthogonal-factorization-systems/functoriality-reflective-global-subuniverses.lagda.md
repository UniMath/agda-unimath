# Functoriality of reflective global subuniverses

```agda
module orthogonal-factorization-systems.functoriality-reflective-global-subuniverses where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-maps
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.retractions
open import foundation.retracts-of-arrows
open import foundation.retracts-of-types
open import foundation.universe-levels

open import orthogonal-factorization-systems.functoriality-localizations-at-global-subuniverses
open import orthogonal-factorization-systems.reflective-global-subuniverses
```

</details>

## Idea

Given a
[reflective global subuniverse](orthogonal-factorization-systems.reflective-global-subuniverses.md)
`𝒫` then for every map `f : X → Y` there is a map `Lf : LX → LY` such that the
square

```text
        f
  X --------> Y
  |           |
  |           |
  ∨    Lf     ∨
  LX ------> LY
```

commutes. This construction preserves identity functions and composition of maps

```text
  L(g ∘ f) ~ Lg ∘ Lf    and    L(id) ~ id
```

## Definitions

### The functorial action on maps of reflective global subuniverses

```agda
module _
  {α β : Level → Level} (𝒫 : reflective-global-subuniverse α β)
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where

  map-reflective-global-subuniverse :
    (X → Y) →
    type-reflection-reflective-global-subuniverse 𝒫 X →
    type-reflection-reflective-global-subuniverse 𝒫 Y
  map-reflective-global-subuniverse =
    map-localization-global-subuniverse
      ( global-subuniverse-reflective-global-subuniverse 𝒫)
      ( is-reflective-reflective-global-subuniverse 𝒫 X)
      ( is-reflective-reflective-global-subuniverse 𝒫 Y)

  eq-naturality-map-reflective-global-subuniverse :
    (f : X → Y) →
    map-reflective-global-subuniverse f ∘
    unit-reflective-global-subuniverse 𝒫 X ＝
    unit-reflective-global-subuniverse 𝒫 Y ∘
    f
  eq-naturality-map-reflective-global-subuniverse =
    eq-naturality-map-localization-global-subuniverse
      ( global-subuniverse-reflective-global-subuniverse 𝒫)
      ( is-reflective-reflective-global-subuniverse 𝒫 X)
      ( is-reflective-reflective-global-subuniverse 𝒫 Y)

  naturality-map-reflective-global-subuniverse :
    (f : X → Y) →
    coherence-square-maps
      ( f)
      ( unit-reflective-global-subuniverse 𝒫 X)
      ( unit-reflective-global-subuniverse 𝒫 Y)
      ( map-reflective-global-subuniverse f)
  naturality-map-reflective-global-subuniverse =
    naturality-map-localization-global-subuniverse
      ( global-subuniverse-reflective-global-subuniverse 𝒫)
      ( is-reflective-reflective-global-subuniverse 𝒫 X)
      ( is-reflective-reflective-global-subuniverse 𝒫 Y)
```

### The functorial action on maps of reflective global subuniverses preserves homotopies

```agda
module _
  {α β : Level → Level} (𝒫 : reflective-global-subuniverse α β)
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where

  preserves-htpy-map-reflective-global-subuniverse :
    {f g : X → Y} → f ~ g →
    map-reflective-global-subuniverse 𝒫 f ~
    map-reflective-global-subuniverse 𝒫 g
  preserves-htpy-map-reflective-global-subuniverse =
    preserves-htpy-map-localization-global-subuniverse
      ( global-subuniverse-reflective-global-subuniverse 𝒫)
      ( is-reflective-reflective-global-subuniverse 𝒫 X)
      ( is-reflective-reflective-global-subuniverse 𝒫 Y)
```

## Properties

### The functorial action on maps of types with localizations preserves identity functions

```agda
module _
  {α β : Level → Level} (𝒫 : reflective-global-subuniverse α β)
  {l1 : Level} {X : UU l1}
  where

  eq-preserves-id-map-reflective-global-subuniverse :
    map-reflective-global-subuniverse 𝒫 (id' X) ＝ id
  eq-preserves-id-map-reflective-global-subuniverse =
    eq-preserves-id-map-localization-global-subuniverse
      ( global-subuniverse-reflective-global-subuniverse 𝒫)
      ( is-reflective-reflective-global-subuniverse 𝒫 X)

  preserves-id-map-reflective-global-subuniverse :
    map-reflective-global-subuniverse 𝒫 (id' X) ~ id
  preserves-id-map-reflective-global-subuniverse =
    preserves-id-map-localization-global-subuniverse
      ( global-subuniverse-reflective-global-subuniverse 𝒫)
      ( is-reflective-reflective-global-subuniverse 𝒫 X)
```

### The functorial action on maps of types with localizations preserves composition

```agda
module _
  {α β : Level → Level} (𝒫 : reflective-global-subuniverse α β)
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} {Z : UU l3}
  (g : Y → Z) (f : X → Y)
  where

  eq-preserves-comp-map-reflective-global-subuniverse :
    map-reflective-global-subuniverse 𝒫 (g ∘ f) ＝
    map-reflective-global-subuniverse 𝒫 g ∘
    map-reflective-global-subuniverse 𝒫 f
  eq-preserves-comp-map-reflective-global-subuniverse =
    eq-preserves-comp-map-localization-global-subuniverse
      ( global-subuniverse-reflective-global-subuniverse 𝒫)
      ( is-reflective-reflective-global-subuniverse 𝒫 X)
      ( is-reflective-reflective-global-subuniverse 𝒫 Y)
      ( is-reflective-reflective-global-subuniverse 𝒫 Z)
      ( g)
      ( f)

  preserves-comp-map-reflective-global-subuniverse :
    map-reflective-global-subuniverse 𝒫 (g ∘ f) ~
    map-reflective-global-subuniverse 𝒫 g ∘
    map-reflective-global-subuniverse 𝒫 f
  preserves-comp-map-reflective-global-subuniverse =
    preserves-comp-map-localization-global-subuniverse
      ( global-subuniverse-reflective-global-subuniverse 𝒫)
      ( is-reflective-reflective-global-subuniverse 𝒫 X)
      ( is-reflective-reflective-global-subuniverse 𝒫 Y)
      ( is-reflective-reflective-global-subuniverse 𝒫 Z)
      ( g)
      ( f)
```

### Reflective global subuniverses are closed under retracts

This is Corollary 5.1.10 in {{#cite Rij19}}.

**Proof.** Let `𝒫` be a reflective global subuniverse and `Y ∈ 𝒫`. Moreover, let
`X` be a retract of `Y`. then applying the functoriality of the reflective
subuniverse we have a retract of maps

```text
        i           r
  X --------> Y --------> X
  |           |           |
  |           |           |
  ∨    Li     ∨    Lr     ∨
  LX -------> LY ------> LX
```

since the middle vertical map is an equivalence, so is the outer vertical map.

```agda
module _
  {α β : Level → Level} (𝒫 : reflective-global-subuniverse α β)
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  (R : X retract-of Y)
  where

  inclusion-retract-reflective-global-subuniverse :
    type-reflection-reflective-global-subuniverse 𝒫 X →
    type-reflection-reflective-global-subuniverse 𝒫 Y
  inclusion-retract-reflective-global-subuniverse =
    map-reflective-global-subuniverse 𝒫 (inclusion-retract R)

  map-retraction-retract-reflective-global-subuniverse :
    type-reflection-reflective-global-subuniverse 𝒫 Y →
    type-reflection-reflective-global-subuniverse 𝒫 X
  map-retraction-retract-reflective-global-subuniverse =
    map-reflective-global-subuniverse 𝒫 (map-retraction-retract R)

  is-retraction-map-retraction-retract-reflective-global-subuniverse :
    is-retraction
      ( inclusion-retract-reflective-global-subuniverse)
      ( map-retraction-retract-reflective-global-subuniverse)
  is-retraction-map-retraction-retract-reflective-global-subuniverse =
    is-retraction-map-retraction-retract-localization-global-subuniverse
      ( global-subuniverse-reflective-global-subuniverse 𝒫)
      ( is-reflective-reflective-global-subuniverse 𝒫 X)
      ( is-reflective-reflective-global-subuniverse 𝒫 Y)
      ( R)

  retraction-retract-reflective-global-subuniverse :
    retraction
      ( inclusion-retract-reflective-global-subuniverse)
  retraction-retract-reflective-global-subuniverse =
    retraction-retract-localization-global-subuniverse
      ( global-subuniverse-reflective-global-subuniverse 𝒫)
      ( is-reflective-reflective-global-subuniverse 𝒫 X)
      ( is-reflective-reflective-global-subuniverse 𝒫 Y)
      ( R)

  retract-reflective-global-subuniverse :
    ( type-reflection-reflective-global-subuniverse 𝒫 X) retract-of
    ( type-reflection-reflective-global-subuniverse 𝒫 Y)
  retract-reflective-global-subuniverse =
    retract-localization-global-subuniverse
      ( global-subuniverse-reflective-global-subuniverse 𝒫)
      ( is-reflective-reflective-global-subuniverse 𝒫 X)
      ( is-reflective-reflective-global-subuniverse 𝒫 Y)
      ( R)

  is-in-reflective-global-subuniverse-retract :
    is-in-reflective-global-subuniverse 𝒫 Y →
    is-in-reflective-global-subuniverse 𝒫 X
  is-in-reflective-global-subuniverse-retract =
    is-in-global-subuniverse-retract-localization-global-subuniverse
      ( global-subuniverse-reflective-global-subuniverse 𝒫)
      ( is-reflective-reflective-global-subuniverse 𝒫 X)
      ( is-reflective-reflective-global-subuniverse 𝒫 Y)
      ( R)
```

## References

{{#bibliography}} {{#reference Rij19}} {{#reference CORS20}}
