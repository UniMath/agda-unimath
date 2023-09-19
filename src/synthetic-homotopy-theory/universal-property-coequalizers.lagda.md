# The universal property of coequalizers

```agda
module synthetic-homotopy-theory.universal-property-coequalizers where
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

open import synthetic-homotopy-theory.coforks
```

</details>

## Idea

Given a parallel pair `f, g : A → B`, consider a
[cofork](synthetic-homotopy-theory.coforks.md) `e : B → X` with vertex X. The
**universal property of coequalizers** is the statement that the cofork
postcomposition map

```text
cofork-map : (X → Y) → cofork Y
```

is an equivalence.

## Definitions

### The universal property of coequalizers

```agda
module _
  { l1 l2 l3 : Level} (l : Level) {A : UU l1} {B : UU l2} (f g : A → B)
  { X : UU l3} (e : cofork f g X)
  where

  universal-property-coequalizer : UU (l1 ⊔ l2 ⊔ l3 ⊔ lsuc l)
  universal-property-coequalizer =
    ( Y : UU l) → is-equiv (cofork-map f g e {Y = Y})

module _
  { l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} (f g : A → B) {X : UU l3}
  ( e : cofork f g X) {Y : UU l4}
  ( up-coequalizer : universal-property-coequalizer l4 f g e)
  where

  map-universal-property-coequalizer : cofork f g Y → (X → Y)
  map-universal-property-coequalizer = map-inv-is-equiv (up-coequalizer Y)
```

## Properties

### The mediating map obtained by the universal property is unique

```agda
module _
  { l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} (f g : A → B) {X : UU l3}
  ( e : cofork f g X) {Y : UU l4}
  ( up-coequalizer : universal-property-coequalizer l4 f g e)
  ( e' : cofork f g Y)
  where

  htpy-cofork-map-universal-property-coequalizer :
    htpy-cofork f g
      ( cofork-map f g e
        ( map-universal-property-coequalizer f g e up-coequalizer e'))
      ( e')
  htpy-cofork-map-universal-property-coequalizer =
    htpy-cofork-eq f g
      ( cofork-map f g e
        ( map-universal-property-coequalizer f g e up-coequalizer e'))
      ( e')
      ( is-section-map-inv-is-equiv (up-coequalizer Y) e')

  abstract
    uniqueness-map-universal-property-coequalizer :
      is-contr (Σ (X → Y) (λ h → htpy-cofork f g (cofork-map f g e h) e'))
    uniqueness-map-universal-property-coequalizer =
      is-contr-is-equiv'
        ( fiber (cofork-map f g e) e')
        ( tot (λ h → htpy-cofork-eq f g (cofork-map f g e h) e'))
        ( is-equiv-tot-is-fiberwise-equiv
          ( λ h → is-equiv-htpy-cofork-eq f g (cofork-map f g e h) e'))
        ( is-contr-map-is-equiv (up-coequalizer Y) e')
```
