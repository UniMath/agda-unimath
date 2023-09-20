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
open import foundation.homotopies
open import foundation.universe-levels

open import synthetic-homotopy-theory.coforks
open import synthetic-homotopy-theory.dependent-coforks
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

  map-dependent-universal-property-coequalizers :
    dependent-cofork f g e P →
    (x : X) → P x
  map-dependent-universal-property-coequalizers =
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

  htpy-dependent-cofork-map-dependent-universal-property-coequalizer :
    htpy-dependent-cofork f g P
      ( dependent-cofork-map f g e
        ( map-dependent-universal-property-coequalizers f g e
          ( dup-coequalizer)
          ( k)))
      ( k)
  htpy-dependent-cofork-map-dependent-universal-property-coequalizer =
    htpy-dependent-cofork-eq f g P
      ( dependent-cofork-map f g e
        ( map-dependent-universal-property-coequalizers f g e
          ( dup-coequalizer)
          ( k)))
      ( k)
      ( is-section-map-inv-is-equiv (dup-coequalizer P) k)

  abstract
    uniqueness-dependent-universal-property-coequalizers :
      is-contr
        ( Σ ((x : X) → P x)
          ( λ h → htpy-dependent-cofork f g P (dependent-cofork-map f g e h) k))
    uniqueness-dependent-universal-property-coequalizers =
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

### The dependent universal property of coequializers implies the universal property of coequalizers

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
      is-equiv-comp-htpy
        ( cofork-map f g e)
        ( map-compute-dependent-cofork-constant-family f g e Y)
        ( dependent-cofork-map f g e)
        ( triangle-compute-dependent-cofork-constant-family f g e Y)
        ( dup-coequalizer (λ _ → Y))
        ( is-equiv-map-equiv
          ( compute-dependent-cofork-constant-family f g e Y))
```
