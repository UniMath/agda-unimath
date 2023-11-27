# The dependent universal property of coequalizers

```agda
module synthetic-homotopy-theory.dependent-universal-property-coequalizers where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.functoriality-dependent-pair-types
open import foundation.universe-levels

open import synthetic-homotopy-theory.26-descent
open import synthetic-homotopy-theory.coforks
open import synthetic-homotopy-theory.dependent-cocones-under-spans
open import synthetic-homotopy-theory.dependent-coforks
open import synthetic-homotopy-theory.dependent-universal-property-pushouts
open import synthetic-homotopy-theory.universal-property-coequalizers
```

</details>

## Idea

The **dependent universal property of coequalizers** is a property of
[coequalizers](synthetic-homotopy-theory.coequalizers.md) of a parallel pair
`f, g : A → B`, asserting that for any type family `P : X → 𝓤` over the
coequalizer `e : B → X`, there is an equivalence between sections of `P` and
dependent cocones on `P` over `e`, given by the map

```text
dependent-cofork-map : ((x : X) → P x) → dependent-cocone e P.
```

## Definitions

### The dependent universal property of coequalizers

```agda
module _
  { l1 l2 l3 : Level} (l : Level) {A : UU l1} {B : UU l2} (f g : A → B)
  { X : UU l3} (e : cofork f g X)
  where

  dependent-universal-property-coequalizer : UU (l1 ⊔ l2 ⊔ l3 ⊔ lsuc l)
  dependent-universal-property-coequalizer =
    (P : X → UU l) → is-equiv (dependent-cofork-map f g e {P = P})

module _
  { l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} (f g : A → B) {X : UU l3}
  ( e : cofork f g X) {P : X → UU l4}
  ( dup-coequalizer : dependent-universal-property-coequalizer l4 f g e)
  where

  map-dependent-universal-property-coequalizer :
    dependent-cofork f g e P →
    (x : X) → P x
  map-dependent-universal-property-coequalizer =
    map-inv-is-equiv (dup-coequalizer P)
```

## Properties

### The mediating dependent map obtained by the dependent universal property is unique

```agda
module _
  { l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} (f g : A → B) {X : UU l3}
  ( e : cofork f g X) {P : X → UU l4}
  ( dup-coequalizer : dependent-universal-property-coequalizer l4 f g e)
  ( k : dependent-cofork f g e P)
  where

  htpy-dependent-cofork-dependent-universal-property-coequalizer :
    htpy-dependent-cofork f g P
      ( dependent-cofork-map f g e
        ( map-dependent-universal-property-coequalizer f g e
          ( dup-coequalizer)
          ( k)))
      ( k)
  htpy-dependent-cofork-dependent-universal-property-coequalizer =
    htpy-dependent-cofork-eq f g P
      ( dependent-cofork-map f g e
        ( map-dependent-universal-property-coequalizer f g e
          ( dup-coequalizer)
          ( k)))
      ( k)
      ( is-section-map-inv-is-equiv (dup-coequalizer P) k)

  abstract
    uniqueness-dependent-universal-property-coequalizer :
      is-contr
        ( Σ ((x : X) → P x)
          ( λ h → htpy-dependent-cofork f g P (dependent-cofork-map f g e h) k))
    uniqueness-dependent-universal-property-coequalizer =
      is-contr-is-equiv'
        ( fiber (dependent-cofork-map f g e) k)
        ( tot
          ( λ h →
            htpy-dependent-cofork-eq f g P (dependent-cofork-map f g e h) k))
        ( is-equiv-tot-is-fiberwise-equiv
          ( λ h →
            is-equiv-htpy-dependent-cofork-eq f g P
              ( dependent-cofork-map f g e h)
              ( k)))
        ( is-contr-map-is-equiv (dup-coequalizer P) k)
```

### A cofork has the dependent universal property of coequalizers if and only if the corresponding cocone has the dependent universal property of pushouts

As mentioned in [coforks](synthetic-homotopy-theory.coforks.md), coforks can be
thought of as special cases of cocones under spans. This theorem makes it more
precise, asserting that under this mapping,
[coequalizers](synthetic-homotopy-theory.coequalizers.md) correspond to
[pushouts](synthetic-homotopy-theory.pushouts.md).

```agda
module _
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (f g : A → B)
  ( e : cofork f g X)
  where

  dependent-universal-property-coequalizer-dependent-universal-property-pushout :
    ( {l : Level} →
      dependent-universal-property-pushout l
        ( vertical-map-span-cocone-cofork f g)
        ( horizontal-map-span-cocone-cofork f g)
        ( cocone-codiagonal-cofork f g e)) →
    ( {l : Level} →
      dependent-universal-property-coequalizer l f g e)
  dependent-universal-property-coequalizer-dependent-universal-property-pushout
    ( dup-pushout)
    ( P) =
    is-equiv-left-map-triangle
      ( dependent-cofork-map f g e)
      ( dependent-cofork-dependent-cocone-codiagonal f g e P)
      ( dependent-cocone-map
        ( vertical-map-span-cocone-cofork f g)
        ( horizontal-map-span-cocone-cofork f g)
        ( cocone-codiagonal-cofork f g e)
        ( P))
      ( triangle-dependent-cofork-dependent-cocone-codiagonal f g e P)
      ( dup-pushout P)
      ( is-equiv-dependent-cofork-dependent-cocone-codiagonal f g e P)

  dependent-universal-property-pushout-dependent-universal-property-coequalizer :
    ( {l : Level} →
      dependent-universal-property-coequalizer l f g e) →
    ( {l : Level} →
      dependent-universal-property-pushout l
        ( vertical-map-span-cocone-cofork f g)
        ( horizontal-map-span-cocone-cofork f g)
        ( cocone-codiagonal-cofork f g e))
  dependent-universal-property-pushout-dependent-universal-property-coequalizer
    ( dup-coequalizer)
    ( P) =
    is-equiv-top-map-triangle
      ( dependent-cofork-map f g e)
      ( dependent-cofork-dependent-cocone-codiagonal f g e P)
      ( dependent-cocone-map
        ( vertical-map-span-cocone-cofork f g)
        ( horizontal-map-span-cocone-cofork f g)
        ( cocone-codiagonal-cofork f g e)
        ( P))
      ( triangle-dependent-cofork-dependent-cocone-codiagonal f g e P)
      ( is-equiv-dependent-cofork-dependent-cocone-codiagonal f g e P)
      ( dup-coequalizer P)
```

### The universal property of coequalizers is equivalent to the dependent universal property of coequalizers

```agda
module _
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f g : A → B) {X : UU l3}
  ( e : cofork f g X)
  where

  universal-property-dependent-universal-property-coequalizer :
    ( {l : Level} → dependent-universal-property-coequalizer l f g e) →
    ( {l : Level} → universal-property-coequalizer l f g e)
  universal-property-dependent-universal-property-coequalizer
    ( dup-coequalizer)
    ( Y) =
    is-equiv-left-map-triangle
      ( cofork-map f g e)
      ( map-compute-dependent-cofork-constant-family f g e Y)
      ( dependent-cofork-map f g e)
      ( triangle-compute-dependent-cofork-constant-family f g e Y)
      ( dup-coequalizer (λ _ → Y))
      ( is-equiv-map-equiv
        ( compute-dependent-cofork-constant-family f g e Y))

  dependent-universal-property-universal-property-coequalizer :
    ( {l : Level} → universal-property-coequalizer l f g e) →
    ( {l : Level} → dependent-universal-property-coequalizer l f g e)
  dependent-universal-property-universal-property-coequalizer up-coequalizer =
    dependent-universal-property-coequalizer-dependent-universal-property-pushout
      ( f)
      ( g)
      ( e)
      ( dependent-universal-property-universal-property-pushout
          ( vertical-map-span-cocone-cofork f g)
          ( horizontal-map-span-cocone-cofork f g)
          ( cocone-codiagonal-cofork f g e)
          ( universal-property-pushout-universal-property-coequalizer f g e
            ( up-coequalizer)))
```
