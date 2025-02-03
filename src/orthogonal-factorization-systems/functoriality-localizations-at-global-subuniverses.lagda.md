# Functoriality of localizations at global subuniverses

```agda
module orthogonal-factorization-systems.functoriality-localizations-at-global-subuniverses where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.commuting-squares-of-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.extensions-types-global-subuniverses
open import foundation.extensions-types-subuniverses
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.global-subuniverses
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.precomposition-functions
open import foundation.propositions
open import foundation.retractions
open import foundation.retracts-of-maps
open import foundation.retracts-of-types
open import foundation.subuniverses
open import foundation.unit-type
open import foundation.universe-levels

open import orthogonal-factorization-systems.localizations-at-global-subuniverses
open import orthogonal-factorization-systems.modal-induction
open import orthogonal-factorization-systems.modal-operators
open import orthogonal-factorization-systems.modal-subuniverse-induction
open import orthogonal-factorization-systems.types-local-at-maps
open import orthogonal-factorization-systems.universal-property-localizations-at-global-subuniverses
```

</details>

## Idea

Given a [global subuniverse](foundation.global-subuniverses.md) `𝒫`, and two
`𝒫`-localizations `η_X : X → LX` and `η_Y : Y → LY` then for every map
`f : X → Y` there is a map `Lf : LX → LY` such that the square

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

### The functorial action on maps of types with localizations

```agda
module _
  {α : Level → Level} (𝒫 : global-subuniverse α)
  {l1 l2 l3 l4 : Level} {X : UU l1} {Y : UU l2}
  (LX : localization-global-subuniverse 𝒫 l3 X)
  (LY : extension-type-global-subuniverse 𝒫 l4 Y)
  where

  map-localization-global-subuniverse' :
    (X → Y) →
    type-localization-global-subuniverse LX →
    type-extension-type-global-subuniverse 𝒫 LY
  map-localization-global-subuniverse' f =
    map-inv-is-equiv
      ( up-localization-global-subuniverse LX
        ( type-global-subuniverse-extension-type-global-subuniverse 𝒫 LY))
      ( inclusion-extension-type-global-subuniverse 𝒫 LY ∘ f)

  eq-naturality-map-localization-global-subuniverse' :
    (f : X → Y) →
    map-localization-global-subuniverse' f ∘
    unit-localization-global-subuniverse LX ＝
    inclusion-extension-type-global-subuniverse 𝒫 LY ∘
    f
  eq-naturality-map-localization-global-subuniverse' f =
    is-section-map-inv-is-equiv
      ( up-localization-global-subuniverse LX
        ( type-global-subuniverse-extension-type-global-subuniverse 𝒫 LY))
      ( inclusion-extension-type-global-subuniverse 𝒫 LY ∘ f)

  naturality-map-localization-global-subuniverse' :
    (f : X → Y) →
    coherence-square-maps
      ( f)
      ( unit-localization-global-subuniverse LX)
      ( inclusion-extension-type-global-subuniverse 𝒫 LY)
      ( map-localization-global-subuniverse' f)
  naturality-map-localization-global-subuniverse' f =
    htpy-eq (eq-naturality-map-localization-global-subuniverse' f)

module _
  {α : Level → Level} (𝒫 : global-subuniverse α)
  {l1 l2 l3 l4 : Level} {X : UU l1} {Y : UU l2}
  (LX : localization-global-subuniverse 𝒫 l3 X)
  (LY : localization-global-subuniverse 𝒫 l4 Y)
  where

  map-localization-global-subuniverse :
    (X → Y) →
    type-localization-global-subuniverse LX →
    type-localization-global-subuniverse LY
  map-localization-global-subuniverse =
    map-localization-global-subuniverse' 𝒫 LX
      ( reflection-localization-global-subuniverse LY)

  eq-naturality-map-localization-global-subuniverse :
    (f : X → Y) →
    map-localization-global-subuniverse f ∘
    unit-localization-global-subuniverse LX ＝
    unit-localization-global-subuniverse LY ∘
    f
  eq-naturality-map-localization-global-subuniverse =
    eq-naturality-map-localization-global-subuniverse' 𝒫 LX
      ( reflection-localization-global-subuniverse LY)

  naturality-map-localization-global-subuniverse :
    (f : X → Y) →
    coherence-square-maps
      ( f)
      ( unit-localization-global-subuniverse LX)
      ( unit-localization-global-subuniverse LY)
      ( map-localization-global-subuniverse f)
  naturality-map-localization-global-subuniverse =
    naturality-map-localization-global-subuniverse' 𝒫 LX
      ( reflection-localization-global-subuniverse LY)
```

### The functorial action on maps of types with localizations preserves homotopies

```agda
module _
  {α : Level → Level} (𝒫 : global-subuniverse α)
  {l1 l2 l3 l4 : Level} {X : UU l1} {Y : UU l2}
  (LX : localization-global-subuniverse 𝒫 l3 X)
  (LY : extension-type-global-subuniverse 𝒫 l4 Y)
  where

  abstract
    preserves-htpy-map-localization-global-subuniverse' :
      {f g : X → Y} → f ~ g →
      map-localization-global-subuniverse' 𝒫 LX LY f ~
      map-localization-global-subuniverse' 𝒫 LX LY g
    preserves-htpy-map-localization-global-subuniverse' {f} =
      ind-htpy f
        ( λ g _ →
          map-localization-global-subuniverse' 𝒫 LX LY f ~
          map-localization-global-subuniverse' 𝒫 LX LY g)
        ( refl-htpy)

module _
  {α : Level → Level} (𝒫 : global-subuniverse α)
  {l1 l2 l3 l4 : Level} {X : UU l1} {Y : UU l2}
  (LX : localization-global-subuniverse 𝒫 l3 X)
  (LY : localization-global-subuniverse 𝒫 l4 Y)
  where

  preserves-htpy-map-localization-global-subuniverse :
    {f g : X → Y} → f ~ g →
    map-localization-global-subuniverse 𝒫 LX LY f ~
    map-localization-global-subuniverse 𝒫 LX LY g
  preserves-htpy-map-localization-global-subuniverse =
    preserves-htpy-map-localization-global-subuniverse' 𝒫 LX
      ( reflection-localization-global-subuniverse LY)
```

## Properties

### The functorial action on maps of types with localizations preserves identity functions

```agda
module _
  {α : Level → Level} (𝒫 : global-subuniverse α)
  {l1 l2 : Level} {X : UU l1}
  (LX : localization-global-subuniverse 𝒫 l2 X)
  where

  eq-preserves-id-map-localization-global-subuniverse :
    map-localization-global-subuniverse 𝒫 LX LX id ＝ id
  eq-preserves-id-map-localization-global-subuniverse =
    is-retraction-map-inv-is-equiv
      ( up-localization-global-subuniverse LX
        ( type-global-subuniverse-localization-global-subuniverse LX))
      ( id)

  preserves-id-map-localization-global-subuniverse :
    map-localization-global-subuniverse 𝒫 LX LX id ~ id
  preserves-id-map-localization-global-subuniverse =
    htpy-eq eq-preserves-id-map-localization-global-subuniverse
```

### The functorial action on maps of types with localizations preserves composition

```agda
module _
  {α : Level → Level} (𝒫 : global-subuniverse α)
  {l1 l2 l3 l4 l5 l6 : Level}
  {X : UU l1} {Y : UU l2} {Z : UU l3}
  (LX : localization-global-subuniverse 𝒫 l4 X)
  (LY : localization-global-subuniverse 𝒫 l5 Y)
  (LZ : extension-type-global-subuniverse 𝒫 l6 Z)
  (g : Y → Z) (f : X → Y)
  where

  eq-preserves-comp-map-localization-global-subuniverse' :
    map-localization-global-subuniverse' 𝒫 LX LZ (g ∘ f) ＝
    map-localization-global-subuniverse' 𝒫 LY LZ g ∘
    map-localization-global-subuniverse 𝒫 LX LY f
  eq-preserves-comp-map-localization-global-subuniverse' =
    equational-reasoning
    map-localization-global-subuniverse' 𝒫 LX LZ (g ∘ f)
    ＝ ( map-inv-is-equiv
        ( up-localization-global-subuniverse LX
          ( type-global-subuniverse-extension-type-global-subuniverse 𝒫 LZ))
        ( map-localization-global-subuniverse' 𝒫 LY LZ g ∘
          map-localization-global-subuniverse 𝒫 LX LY f ∘
          unit-localization-global-subuniverse LX))
    by
      ap
        ( map-inv-is-equiv
          ( up-localization-global-subuniverse LX
            ( type-global-subuniverse-extension-type-global-subuniverse 𝒫 LZ)))
        ( inv
          ( ap
            ( map-localization-global-subuniverse' 𝒫 LY LZ g ∘_)
            ( eq-naturality-map-localization-global-subuniverse 𝒫 LX LY f) ∙
            ap
              ( _∘ f)
              ( eq-naturality-map-localization-global-subuniverse' 𝒫 LY LZ g)))
    ＝ ( map-localization-global-subuniverse' 𝒫 LY LZ g ∘
        map-localization-global-subuniverse 𝒫 LX LY f)
    by
      ( is-retraction-map-inv-is-equiv
        ( up-localization-global-subuniverse LX
          ( type-global-subuniverse-extension-type-global-subuniverse 𝒫 LZ))
        ( map-localization-global-subuniverse' 𝒫 LY LZ g ∘
          map-localization-global-subuniverse 𝒫 LX LY f))

  preserves-comp-map-localization-global-subuniverse' :
    map-localization-global-subuniverse' 𝒫 LX LZ (g ∘ f) ~
    map-localization-global-subuniverse' 𝒫 LY LZ g ∘
    map-localization-global-subuniverse 𝒫 LX LY f
  preserves-comp-map-localization-global-subuniverse' =
    htpy-eq eq-preserves-comp-map-localization-global-subuniverse'

module _
  {α : Level → Level} (𝒫 : global-subuniverse α)
  {l1 l2 l3 l4 l5 l6 : Level}
  {X : UU l1} {Y : UU l2} {Z : UU l3}
  (LX : localization-global-subuniverse 𝒫 l4 X)
  (LY : localization-global-subuniverse 𝒫 l5 Y)
  (LZ : localization-global-subuniverse 𝒫 l6 Z)
  (g : Y → Z) (f : X → Y)
  where

  eq-preserves-comp-map-localization-global-subuniverse :
    map-localization-global-subuniverse 𝒫 LX LZ (g ∘ f) ＝
    map-localization-global-subuniverse 𝒫 LY LZ g ∘
    map-localization-global-subuniverse 𝒫 LX LY f
  eq-preserves-comp-map-localization-global-subuniverse =
    eq-preserves-comp-map-localization-global-subuniverse' 𝒫
      LX LY (reflection-localization-global-subuniverse LZ) g f

  preserves-comp-map-localization-global-subuniverse :
    map-localization-global-subuniverse 𝒫 LX LZ (g ∘ f) ~
    map-localization-global-subuniverse 𝒫 LY LZ g ∘
    map-localization-global-subuniverse 𝒫 LX LY f
  preserves-comp-map-localization-global-subuniverse =
    preserves-comp-map-localization-global-subuniverse' 𝒫
      LX LY (reflection-localization-global-subuniverse LZ) g f
```

### Localizations are closed under retracts

**Proof.** Let `X` and `Y` be types with localizations in a global subuniverse
`𝒫`. Moreover, assume `X` is a retract of `Y` and that `Y ∈ 𝒫`. then applying
the functoriality of localizations at global subuniverses we have a retract of
maps

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
  {α : Level → Level} (𝒫 : global-subuniverse α)
  {l1 l2 l3 l4 : Level} {X : UU l1} {Y : UU l2}
  (LX : localization-global-subuniverse 𝒫 l3 X)
  (LY : localization-global-subuniverse 𝒫 l4 Y)
  (R : X retract-of Y)
  where

  inclusion-retract-localization-global-subuniverse :
    type-localization-global-subuniverse LX →
    type-localization-global-subuniverse LY
  inclusion-retract-localization-global-subuniverse =
    map-localization-global-subuniverse 𝒫 LX LY (inclusion-retract R)

  map-retraction-retract-localization-global-subuniverse :
    type-localization-global-subuniverse LY →
    type-localization-global-subuniverse LX
  map-retraction-retract-localization-global-subuniverse =
    map-localization-global-subuniverse 𝒫 LY LX (map-retraction-retract R)

  is-retraction-map-retraction-retract-localization-global-subuniverse :
    is-retraction
      ( inclusion-retract-localization-global-subuniverse)
      ( map-retraction-retract-localization-global-subuniverse)
  is-retraction-map-retraction-retract-localization-global-subuniverse =
    inv-htpy
      ( preserves-comp-map-localization-global-subuniverse 𝒫 LX LY LX
        ( map-retraction-retract R)
        ( inclusion-retract R)) ∙h
    preserves-htpy-map-localization-global-subuniverse 𝒫 LX LX
      ( is-retraction-map-retraction-retract R) ∙h
    preserves-id-map-localization-global-subuniverse 𝒫 LX

  retraction-retract-localization-global-subuniverse :
    retraction
      ( inclusion-retract-localization-global-subuniverse)
  retraction-retract-localization-global-subuniverse =
    map-retraction-retract-localization-global-subuniverse ,
    is-retraction-map-retraction-retract-localization-global-subuniverse

  retract-localization-global-subuniverse :
    ( type-localization-global-subuniverse LX) retract-of
    ( type-localization-global-subuniverse LY)
  retract-localization-global-subuniverse =
    ( map-localization-global-subuniverse 𝒫 LX LY (inclusion-retract R)) ,
    ( retraction-retract-localization-global-subuniverse)

  is-in-global-subuniverse-retract-localization-global-subuniverse :
    is-in-global-subuniverse 𝒫 Y →
    is-in-global-subuniverse 𝒫 X
  is-in-global-subuniverse-retract-localization-global-subuniverse H =
    is-in-global-subuniverse-is-equiv-unit-universal-property-localization-global-subuniverse
      ( 𝒫)
      ( reflection-localization-global-subuniverse LX)
      ( up-localization-global-subuniverse LX)
      ( is-equiv-retract-map-is-equiv'
        ( unit-localization-global-subuniverse LX)
        ( unit-localization-global-subuniverse LY)
        ( R)
        ( retract-localization-global-subuniverse)
        ( naturality-map-localization-global-subuniverse 𝒫 LX LY
          ( inclusion-retract R))
        ( naturality-map-localization-global-subuniverse 𝒫 LY LX
          ( map-retraction-retract R))
        ( is-equiv-unit-is-in-global-subuniverse-universal-property-localization-global-subuniverse
          ( 𝒫)
          ( reflection-localization-global-subuniverse LY)
          ( up-localization-global-subuniverse LY)
          ( H)))
```

## References

{{#bibliography}} {{#reference Rij19}} {{#reference CORS20}}
