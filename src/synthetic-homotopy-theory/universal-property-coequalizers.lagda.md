# The universal property of coequalizers

```agda
module synthetic-homotopy-theory.universal-property-coequalizers where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.homotopies-morphisms-arrows
open import foundation.identity-types
open import foundation.morphisms-arrows
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-span-diagrams
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

is an [equivalence](foundation.equivalences.md).

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

### In a cofork on equivalences in the category of arrows, the domain cofork is a coequalizer if and only if the codomain cofork is a coequalizer

In other words, given two coforks connected vertically with equivalences, as in
the following diagram:

```text
    ----->
  A -----> B -----> C
  |        |        |
 ≃|        |≃       |≃
  V  ----> V        V
  A' ----> B' ----> C' ,
```

equipped with [commuting squares](foundation.commuting-squares-of-maps.md) for
the three small squares, and a coherence datum expressing that the right square
coequalizes the left squares in the category of arrows, we have that the top
cofork is a coequalizer if and only if the bottom cofork is a coequalizer.

```agda
module _
  { l1 l2 l3 l4 l5 l6 : Level}
  { A : UU l1} {B : UU l2} {C : UU l3}
  { A' : UU l4} {B' : UU l5} {C' : UU l6}
  ( hA : A → A') (hB : B → B') (hC : C → C')
  ( f : hom-arrow hA hB) (g : hom-arrow hA hB) (c : hom-arrow hB hC)
  ( H :
    htpy-hom-arrow hA hC
      ( comp-hom-arrow hA hB hC c f)
      ( comp-hom-arrow hA hB hC c g))
  ( is-equiv-hA : is-equiv hA) (is-equiv-hB : is-equiv hB)
  ( is-equiv-hC : is-equiv hC)
  where

  top-cofork-hom-arrow :
    cofork (map-domain-hom-arrow hA hB f) (map-domain-hom-arrow hA hB g) C
  pr1 top-cofork-hom-arrow = map-domain-hom-arrow hB hC c
  pr2 top-cofork-hom-arrow = htpy-domain-htpy-hom-arrow hA hC _ _ H

  bottom-cofork-hom-arrow :
    cofork (map-codomain-hom-arrow hA hB f) (map-codomain-hom-arrow hA hB g) C'
  pr1 bottom-cofork-hom-arrow = map-codomain-hom-arrow hB hC c
  pr2 bottom-cofork-hom-arrow = htpy-codomain-htpy-hom-arrow hA hC _ _ H

  universal-property-coequalizer-top-universal-property-coequalizer-bottom-hom-arrow-is-equiv :
    ({l : Level} →
      universal-property-coequalizer l _ _ bottom-cofork-hom-arrow) →
    ({l : Level} → universal-property-coequalizer l _ _ top-cofork-hom-arrow)
  universal-property-coequalizer-top-universal-property-coequalizer-bottom-hom-arrow-is-equiv
    ( up-c') =
    universal-property-coequalizer-universal-property-pushout _ _
      ( top-cofork-hom-arrow)
      ( universal-property-pushout-top-universal-property-pushout-bottom-cube-is-equiv
        ( vertical-map-span-cocone-cofork
          ( map-codomain-hom-arrow hA hB f)
          ( map-codomain-hom-arrow hA hB g))
        ( horizontal-map-span-cocone-cofork
          ( map-codomain-hom-arrow hA hB f)
          ( map-codomain-hom-arrow hA hB g))
        ( horizontal-map-cocone-cofork _ _ bottom-cofork-hom-arrow)
        ( vertical-map-cocone-cofork _ _ bottom-cofork-hom-arrow)
        ( vertical-map-span-cocone-cofork
          ( map-domain-hom-arrow hA hB f)
          ( map-domain-hom-arrow hA hB g))
        ( horizontal-map-span-cocone-cofork
          ( map-domain-hom-arrow hA hB f)
          ( map-domain-hom-arrow hA hB g))
        ( horizontal-map-cocone-cofork _ _ top-cofork-hom-arrow)
        ( vertical-map-cocone-cofork _ _ top-cofork-hom-arrow)
        ( map-coproduct hA hA)
        ( hA)
        ( hB)
        ( hC)
        ( coherence-square-cocone-cofork _ _ top-cofork-hom-arrow)
        ( ind-coproduct _ refl-htpy refl-htpy)
        ( ind-coproduct _ (coh-hom-arrow hA hB f) (coh-hom-arrow hA hB g))
        ( coh-comp-hom-arrow hA hB hC c f)
        ( coh-hom-arrow hB hC c)
        ( coherence-square-cocone-cofork _ _ bottom-cofork-hom-arrow)
        ( ind-coproduct _ (λ _ → right-unit) (coh-htpy-hom-arrow hA hC _ _ H))
        ( is-equiv-map-coproduct is-equiv-hA is-equiv-hA)
        ( is-equiv-hA)
        ( is-equiv-hB)
        ( is-equiv-hC)
        ( universal-property-pushout-universal-property-coequalizer _ _
          ( bottom-cofork-hom-arrow)
          ( up-c')))

  universal-property-coequalizer-bottom-universal-property-coequalizer-top-hom-arrow-is-equiv :
    ({l : Level} → universal-property-coequalizer l _ _ top-cofork-hom-arrow) →
    ({l : Level} → universal-property-coequalizer l _ _ bottom-cofork-hom-arrow)
  universal-property-coequalizer-bottom-universal-property-coequalizer-top-hom-arrow-is-equiv
    ( up-c) =
    universal-property-coequalizer-universal-property-pushout _ _
      ( bottom-cofork-hom-arrow)
      ( universal-property-pushout-bottom-universal-property-pushout-top-cube-is-equiv
        ( vertical-map-span-cocone-cofork
          ( map-codomain-hom-arrow hA hB f)
          ( map-codomain-hom-arrow hA hB g))
        ( horizontal-map-span-cocone-cofork
          ( map-codomain-hom-arrow hA hB f)
          ( map-codomain-hom-arrow hA hB g))
        ( horizontal-map-cocone-cofork _ _ bottom-cofork-hom-arrow)
        ( vertical-map-cocone-cofork _ _ bottom-cofork-hom-arrow)
        ( vertical-map-span-cocone-cofork
          ( map-domain-hom-arrow hA hB f)
          ( map-domain-hom-arrow hA hB g))
        ( horizontal-map-span-cocone-cofork
          ( map-domain-hom-arrow hA hB f)
          ( map-domain-hom-arrow hA hB g))
        ( horizontal-map-cocone-cofork _ _ top-cofork-hom-arrow)
        ( vertical-map-cocone-cofork _ _ top-cofork-hom-arrow)
        ( map-coproduct hA hA)
        ( hA)
        ( hB)
        ( hC)
        ( coherence-square-cocone-cofork _ _ top-cofork-hom-arrow)
        ( ind-coproduct _ refl-htpy refl-htpy)
        ( ind-coproduct _ (coh-hom-arrow hA hB f) (coh-hom-arrow hA hB g))
        ( coh-comp-hom-arrow hA hB hC c f)
        ( coh-hom-arrow hB hC c)
        ( coherence-square-cocone-cofork _ _ bottom-cofork-hom-arrow)
        ( ind-coproduct _ (λ _ → right-unit) (coh-htpy-hom-arrow hA hC _ _ H))
        ( is-equiv-map-coproduct is-equiv-hA is-equiv-hA)
        ( is-equiv-hA)
        ( is-equiv-hB)
        ( is-equiv-hC)
        ( universal-property-pushout-universal-property-coequalizer _ _
          ( top-cofork-hom-arrow)
          ( up-c)))
```
