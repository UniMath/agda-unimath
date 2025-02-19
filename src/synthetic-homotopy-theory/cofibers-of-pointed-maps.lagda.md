# Cofibers of pointed maps

```agda
module synthetic-homotopy-theory.cofibers-of-pointed-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.constant-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.unit-type
open import foundation.universe-levels

open import structured-types.pointed-maps
open import structured-types.pointed-types
open import structured-types.pointed-unit-type

open import synthetic-homotopy-theory.cocones-under-pointed-span-diagrams
open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.cofibers-of-maps
open import synthetic-homotopy-theory.dependent-cocones-under-spans
open import synthetic-homotopy-theory.dependent-universal-property-pushouts
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.pushouts-of-pointed-types
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

## Idea

The
{{#concept "cofiber" Disambiguation="of a pointed map of pointed types" WD="mapping cone" WDID=Q306560 Agda=cofiber-Pointed-Type}}
of a [pointed map](structured-types.pointed-maps.md) `f : A →∗ B` is the
[pushout](synthetic-homotopy-theory.pushouts-of-pointed-types.md) of the span of
pointed maps `B ← A → *`.

## Definitions

### The cofiber of a pointed map

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2} (f : A →∗ B)
  where

  type-cofiber-Pointed-Type : UU (l1 ⊔ l2)
  type-cofiber-Pointed-Type =
    type-pushout-Pointed-Type f (terminal-pointed-map A)

  point-cofiber-Pointed-Type : Pointed-Type (l1 ⊔ l2)
  point-cofiber-Pointed-Type = pushout-Pointed-Type f (terminal-pointed-map A)

  cofiber-Pointed-Type : Pointed-Type (l1 ⊔ l2)
  cofiber-Pointed-Type = pushout-Pointed-Type f (terminal-pointed-map A)

  inl-cofiber-Pointed-Type : B →∗ cofiber-Pointed-Type
  inl-cofiber-Pointed-Type = inl-pushout-Pointed-Type f (terminal-pointed-map A)

  inr-cofiber-Pointed-Type : unit-Pointed-Type →∗ cofiber-Pointed-Type
  inr-cofiber-Pointed-Type = inr-pushout-Pointed-Type f (terminal-pointed-map A)

  map-cogap-cofiber-Pointed-Type :
    {l : Level} {X : Pointed-Type l} →
    cocone-Pointed-Type f (terminal-pointed-map A) X →
    type-cofiber-Pointed-Type → type-Pointed-Type X
  map-cogap-cofiber-Pointed-Type =
    map-cogap-Pointed-Type f (terminal-pointed-map A)

  cogap-cofiber-Pointed-Type :
    {l : Level} {X : Pointed-Type l} →
    cocone-Pointed-Type f (terminal-pointed-map A) X →
    cofiber-Pointed-Type →∗ X
  cogap-cofiber-Pointed-Type = cogap-Pointed-Type f (terminal-pointed-map A)
```
