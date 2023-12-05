# The universal property of coequalizers

```agda
module synthetic-homotopy-theory.universal-property-coequalizers where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-maps
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels
open import foundation.whiskering-homotopies

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.coforks
open import synthetic-homotopy-theory.universal-property-pushouts
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

### A cofork has the universal property of coequalizers if and only if the corresponding cocone has the universal property of pushouts

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

  universal-property-coequalizer-universal-property-pushout :
    ( {l : Level} →
      universal-property-pushout l
        ( vertical-map-span-cocone-cofork f g)
        ( horizontal-map-span-cocone-cofork f g)
        ( cocone-codiagonal-cofork f g e)) →
    ( {l : Level} →
      universal-property-coequalizer l f g e)
  universal-property-coequalizer-universal-property-pushout up-pushout Y =
    is-equiv-left-map-triangle
      ( cofork-map f g e)
      ( cofork-cocone-codiagonal f g)
      ( cocone-map
        ( vertical-map-span-cocone-cofork f g)
        ( horizontal-map-span-cocone-cofork f g)
        ( cocone-codiagonal-cofork f g e))
      ( triangle-cofork-cocone f g e)
      ( up-pushout Y)
      ( is-equiv-cofork-cocone-codiagonal f g)

  universal-property-pushout-universal-property-coequalizer :
    ( {l : Level} →
      universal-property-coequalizer l f g e) →
    ( {l : Level} →
      universal-property-pushout l
        ( vertical-map-span-cocone-cofork f g)
        ( horizontal-map-span-cocone-cofork f g)
        ( cocone-codiagonal-cofork f g e))
  universal-property-pushout-universal-property-coequalizer up-coequalizer Y =
    is-equiv-top-map-triangle
      ( cofork-map f g e)
      ( cofork-cocone-codiagonal f g)
      ( cocone-map
        ( vertical-map-span-cocone-cofork f g)
        ( horizontal-map-span-cocone-cofork f g)
        ( cocone-codiagonal-cofork f g e))
      ( triangle-cofork-cocone f g e)
      ( is-equiv-cofork-cocone-codiagonal f g)
      ( up-coequalizer Y)
```

### In a commuting (something) where the vertical maps are equivalences, the bottom cofork is a coequalizer if and only if the top cofork is a coequalizer

```agda
module _
  { l1 l2 l3 l4 l5 l6 : Level}
  { A : UU l1} {B : UU l2} {C : UU l3}
  ( f : A → B) (g : A → B) (c : cofork f g C)
  { A' : UU l4} {B' : UU l5} {C' : UU l6}
  ( f' : A' → B') (g' : A' → B') (c' : cofork f' g' C')
  ( hA : A → A') (hB : B → B') (hC : C → C')
  ( left-front : coherence-square-maps f hA hB f')
  ( left-back : coherence-square-maps g hA hB g')
  ( right :
      coherence-square-maps (map-cofork f g c) hB hC (map-cofork f' g' c'))
  ( barrel :
    ( ( pasting-horizontal-coherence-square-maps f
        ( map-cofork f g c)
        ( hA)
        ( hB)
        ( hC)
        ( f')
        ( map-cofork f' g' c')
        ( left-front)
        ( right) ∙h
      ( hC ·l (coherence-cofork f g c)))) ~
    ( ( coherence-cofork f' g' c' ·r hA) ∙h
      ( pasting-horizontal-coherence-square-maps g
        ( map-cofork f g c)
        ( hA)
        ( hB)
        ( hC)
        ( g')
        ( map-cofork f' g' c')
        ( left-back)
        ( right))))
  ( is-equiv-hA : is-equiv hA) (is-equiv-hB : is-equiv hB)
  ( is-equiv-hC : is-equiv hC)
  where

  universal-property-coequalizer-top-universal-property-coequalizer-bottom-is-equiv :
    ({l : Level} → universal-property-coequalizer l f' g' c') →
    ({l : Level} → universal-property-coequalizer l f g c)
  universal-property-coequalizer-top-universal-property-coequalizer-bottom-is-equiv
    ( up-c') =
    universal-property-coequalizer-universal-property-pushout f g c
      ( universal-property-pushout-top-universal-property-pushout-bottom-cube-is-equiv
        ( vertical-map-span-cocone-cofork f' g')
        ( horizontal-map-span-cocone-cofork f' g')
        ( horizontal-map-cocone-cofork f' g' c')
        ( vertical-map-cocone-cofork f' g' c')
        ( vertical-map-span-cocone-cofork f g)
        ( horizontal-map-span-cocone-cofork f g)
        ( horizontal-map-cocone-cofork f g c)
        ( vertical-map-cocone-cofork f g c)
        ( map-coprod hA hA)
        ( hA)
        ( hB)
        ( hC)
        ( coherence-square-cocone-cofork f g c)
        ( λ where
          (inl a) → refl
          (inr a) → refl)
        ( λ where
          (inl a) → left-front a
          (inr a) → left-back a)
        ( pasting-horizontal-coherence-square-maps f
          ( map-cofork f g c)
          ( hA)
          ( hB)
          ( hC)
          ( f')
          ( map-cofork f' g' c')
          ( left-front)
          ( right))
        ( right)
        ( coherence-square-cocone-cofork f' g' c')
        ( λ where
          (inl a) → right-unit
          (inr a) → barrel a)
        ( is-equiv-map-coprod is-equiv-hA is-equiv-hA)
        ( is-equiv-hA)
        ( is-equiv-hB)
        ( is-equiv-hC)
        ( universal-property-pushout-universal-property-coequalizer f' g' c'
          ( up-c')))

  universal-property-coequalizer-bottom-universal-property-coequalizer-top-is-equiv :
    ({l : Level} → universal-property-coequalizer l f g c) →
    ({l : Level} → universal-property-coequalizer l f' g' c')
  universal-property-coequalizer-bottom-universal-property-coequalizer-top-is-equiv
    ( up-c) =
    universal-property-coequalizer-universal-property-pushout f' g' c'
      ( universal-property-pushout-bottom-universal-property-pushout-top-cube-is-equiv
        ( vertical-map-span-cocone-cofork f' g')
        ( horizontal-map-span-cocone-cofork f' g')
        ( horizontal-map-cocone-cofork f' g' c')
        ( vertical-map-cocone-cofork f' g' c')
        ( vertical-map-span-cocone-cofork f g)
        ( horizontal-map-span-cocone-cofork f g)
        ( horizontal-map-cocone-cofork f g c)
        ( vertical-map-cocone-cofork f g c)
        ( map-coprod hA hA)
        ( hA)
        ( hB)
        ( hC)
        ( coherence-square-cocone-cofork f g c)
        ( λ where
          (inl a) → refl
          (inr a) → refl)
        ( λ where
          (inl a) → left-front a
          (inr a) → left-back a)
        ( pasting-horizontal-coherence-square-maps f
          ( map-cofork f g c)
          ( hA)
          ( hB)
          ( hC)
          ( f')
          ( map-cofork f' g' c')
          ( left-front)
          ( right))
        ( right)
        ( coherence-square-cocone-cofork f' g' c')
        ( λ where
          (inl a) → right-unit
          (inr a) → barrel a)
        ( is-equiv-map-coprod is-equiv-hA is-equiv-hA)
        ( is-equiv-hA)
        ( is-equiv-hB)
        ( is-equiv-hC)
        ( universal-property-pushout-universal-property-coequalizer f g c up-c))
```
