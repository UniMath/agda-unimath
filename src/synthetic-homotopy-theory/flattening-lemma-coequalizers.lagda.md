# The flattening lemma for coequalizers

```agda
{-# OPTIONS --lossy-unification #-}
module synthetic-homotopy-theory.flattening-lemma-coequalizers where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-triangles-of-identifications
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.double-arrows
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.equivalences-double-arrows
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-coproduct-types
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition
open import foundation.whiskering-identifications-concatenation

open import synthetic-homotopy-theory.coforks
open import synthetic-homotopy-theory.dependent-universal-property-coequalizers
open import synthetic-homotopy-theory.descent-data-coequalizers
open import synthetic-homotopy-theory.equivalences-coforks-under-equivalences-double-arrows
open import synthetic-homotopy-theory.equivalences-descent-data-coequalizers
open import synthetic-homotopy-theory.flattening-lemma-pushouts
open import synthetic-homotopy-theory.universal-property-coequalizers
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

## Idea

The
{{#concept "flattening lemma" Disambiguation="coequalizers" Agda=flattening-lemma-coequalizer}}
for [coequalizers](synthetic-homotopy-theory.coequalizers.md) states that
coequalizers commute with
[dependent pair types](foundation.dependent-pair-types.md). More precisely,
given a coequalizer

```text
     g
   ----->     e
 A -----> B -----> X
     f
```

with homotopy `H : e ∘ f ~ e ∘ g`, and a type family `P : X → 𝓤` over `X`, the
cofork

```text
                  ----->
 Σ (a : A) P(efa) -----> Σ (b : B) P(eb) ---> Σ (x : X) P(x)
```

is again a coequalizer.

## Definitions

### The statement of the flattening lemma for coequalizers

```agda
module _
  {l1 l2 l3 l4 : Level} (a : double-arrow l1 l2) {X : UU l3}
  (P : X → UU l4) (e : cofork a X)
  where

  left-map-double-arrow-flattening-lemma-coequalizer :
    Σ (domain-double-arrow a) (P ∘ map-cofork e ∘ left-map-double-arrow a) →
    Σ (codomain-double-arrow a) (P ∘ map-cofork e)
  left-map-double-arrow-flattening-lemma-coequalizer =
    map-Σ-map-base
      ( left-map-double-arrow a)
      ( P ∘ map-cofork e)

  right-map-double-arrow-flattening-lemma-coequalizer :
    Σ (domain-double-arrow a) (P ∘ map-cofork e ∘ left-map-double-arrow a) →
    Σ (codomain-double-arrow a) (P ∘ map-cofork e)
  right-map-double-arrow-flattening-lemma-coequalizer =
    map-Σ
      ( P ∘ map-cofork e)
      ( right-map-double-arrow a)
      ( λ x → tr P (coh-cofork e x))

  double-arrow-flattening-lemma-coequalizer : double-arrow (l1 ⊔ l4) (l2 ⊔ l4)
  double-arrow-flattening-lemma-coequalizer =
    make-double-arrow
      ( left-map-double-arrow-flattening-lemma-coequalizer)
      ( right-map-double-arrow-flattening-lemma-coequalizer)

  cofork-flattening-lemma-coequalizer :
    cofork double-arrow-flattening-lemma-coequalizer (Σ X P)
  pr1 cofork-flattening-lemma-coequalizer = map-Σ-map-base (map-cofork e) P
  pr2 cofork-flattening-lemma-coequalizer =
    coherence-square-maps-map-Σ-map-base P
      ( right-map-double-arrow a)
      ( left-map-double-arrow a)
      ( map-cofork e)
      ( map-cofork e)
      ( coh-cofork e)

  flattening-lemma-coequalizer-statement : UUω
  flattening-lemma-coequalizer-statement =
    dependent-universal-property-coequalizer e →
    universal-property-coequalizer (cofork-flattening-lemma-coequalizer)
```

### The statement of the flattening lemma for coequalizers, phrased using descent data

The above statement of the flattening lemma works with a provided type family
over the coequalizer. We can instead accept a definition of this family via
descent data.

```agda
module _
  {l1 l2 l3 : Level} {F : double-arrow l1 l2}
  (P : descent-data-coequalizer F l3)
  where

  double-arrow-flattening-lemma-descent-data-coequalizer :
    double-arrow (l1 ⊔ l3) (l2 ⊔ l3)
  double-arrow-flattening-lemma-descent-data-coequalizer =
    make-double-arrow
      ( map-Σ-map-base
        ( left-map-double-arrow F)
        ( family-descent-data-coequalizer P))
      ( map-Σ
        ( family-descent-data-coequalizer P)
        ( right-map-double-arrow F)
        ( map-family-descent-data-coequalizer P))

module _
  {l1 l2 l3 l4 : Level} {F : double-arrow l1 l2}
  {X : UU l3} (c : cofork F X)
  (P : descent-data-coequalizer F l4)
  (Q : X → UU l4)
  (e : equiv-descent-data-coequalizer P (descent-data-family-cofork c Q))
  where

  cofork-flattening-lemma-descent-coequalizer :
    cofork
      ( double-arrow-flattening-lemma-descent-data-coequalizer P)
      ( Σ X Q)
  pr1 cofork-flattening-lemma-descent-coequalizer =
    map-Σ Q
      ( map-cofork c)
      ( map-equiv-descent-data-coequalizer P (descent-data-family-cofork c Q) e)
  pr2 cofork-flattening-lemma-descent-coequalizer =
    coherence-square-maps-Σ Q
      ( map-family-descent-data-coequalizer P)
      ( λ a → id)
      ( map-equiv-descent-data-coequalizer P (descent-data-family-cofork c Q) e)
      ( map-equiv-descent-data-coequalizer P (descent-data-family-cofork c Q) e)
      ( λ a →
        inv-htpy
          ( coherence-equiv-descent-data-coequalizer P
            ( descent-data-family-cofork c Q)
            ( e)
            ( a)))

  flattening-lemma-descent-data-coequalizer-statement : UUω
  flattening-lemma-descent-data-coequalizer-statement =
    universal-property-coequalizer c →
    universal-property-coequalizer cofork-flattening-lemma-descent-coequalizer
```

## Properties

### Proof of the flattening lemma for coequalizers

To show that the cofork of total spaces is a coequalizer, it
[suffices to show](synthetic-homotopy-theory.universal-property-coequalizers.md)
that the induced cocone is a pushout. This is accomplished by constructing a
[commuting cube](foundation.commuting-cubes-of-maps.md) where the bottom is this
cocone, and the top is the cocone of total spaces for the cocone induced by the
cofork.

Assuming that the given cofork is a coequalizer, we get that its induced cocone
is a pushout, so by the
[flattening lemma for pushouts](synthetic-homotopy-theory.flattening-lemma-pushouts.md),
the top square is a pushout as well. The vertical maps of the cube are
[equivalences](foundation.equivalences.md), so it follows that the bottom square
is a pushout.

```agda
module _
  { l1 l2 l3 l4 : Level} (a : double-arrow l1 l2) {X : UU l3}
  ( P : X → UU l4) (e : cofork a X)
  where

  abstract
    flattening-lemma-coequalizer : flattening-lemma-coequalizer-statement a P e
    flattening-lemma-coequalizer dup-coequalizer =
      universal-property-coequalizer-universal-property-pushout
        ( universal-property-pushout-bottom-universal-property-pushout-top-cube-is-equiv
          ( vertical-map-span-cocone-cofork
            ( double-arrow-flattening-lemma-coequalizer a P e))
          ( horizontal-map-span-cocone-cofork
            ( double-arrow-flattening-lemma-coequalizer a P e))
          ( horizontal-map-cocone-flattening-pushout P
            ( vertical-map-span-cocone-cofork a)
            ( horizontal-map-span-cocone-cofork a)
            ( cocone-codiagonal-cofork a e))
          ( vertical-map-cocone-flattening-pushout P
            ( vertical-map-span-cocone-cofork a)
            ( horizontal-map-span-cocone-cofork a)
            ( cocone-codiagonal-cofork a e))
          ( vertical-map-span-flattening-pushout P
            ( vertical-map-span-cocone-cofork a)
            ( horizontal-map-span-cocone-cofork a)
            ( cocone-codiagonal-cofork a e))
          ( horizontal-map-span-flattening-pushout P
            ( vertical-map-span-cocone-cofork a)
            ( horizontal-map-span-cocone-cofork a)
            ( cocone-codiagonal-cofork a e))
          ( horizontal-map-cocone-flattening-pushout P
            ( vertical-map-span-cocone-cofork a)
            ( horizontal-map-span-cocone-cofork a)
            ( cocone-codiagonal-cofork a e))
          ( vertical-map-cocone-flattening-pushout P
            ( vertical-map-span-cocone-cofork a)
            ( horizontal-map-span-cocone-cofork a)
            ( cocone-codiagonal-cofork a e))
          ( map-equiv
            ( right-distributive-Σ-coproduct
              ( domain-double-arrow a)
              ( domain-double-arrow a)
              ( ( P) ∘
                ( horizontal-map-cocone-cofork a e) ∘
                ( vertical-map-span-cocone-cofork a))))
          ( id)
          ( id)
          ( id)
          ( coherence-square-cocone-flattening-pushout P
            ( vertical-map-span-cocone-cofork a)
            ( horizontal-map-span-cocone-cofork a)
            ( cocone-codiagonal-cofork a e))
          ( ind-Σ (ind-coproduct _ (ev-pair refl-htpy) (ev-pair refl-htpy)))
          ( ind-Σ (ind-coproduct _ (ev-pair refl-htpy) (ev-pair refl-htpy)))
          ( refl-htpy)
          ( refl-htpy)
          ( coherence-square-cocone-cofork
            ( double-arrow-flattening-lemma-coequalizer a P e)
            ( cofork-flattening-lemma-coequalizer a P e))
          ( ind-Σ
            ( ind-coproduct _
              ( ev-pair refl-htpy)
              ( ev-pair (λ t → ap-id _ ∙ inv right-unit))))
          ( is-equiv-map-equiv
            ( right-distributive-Σ-coproduct
              ( domain-double-arrow a)
              ( domain-double-arrow a)
              ( ( P) ∘
                ( horizontal-map-cocone-cofork a e) ∘
                ( vertical-map-span-cocone-cofork a))))
          ( is-equiv-id)
          ( is-equiv-id)
          ( is-equiv-id)
          ( flattening-lemma-pushout P
            ( vertical-map-span-cocone-cofork a)
            ( horizontal-map-span-cocone-cofork a)
            ( cocone-codiagonal-cofork a e)
            ( dependent-universal-property-pushout-dependent-universal-property-coequalizer
              ( dup-coequalizer))))
```

### Proof of the descent data statement of the flattening lemma for coequalizers

```agda
module _
  {l1 l2 l3 l4 : Level} {F : double-arrow l1 l2}
  {X : UU l3} {c : cofork F X}
  (P : descent-data-coequalizer F l4)
  (Q : X → UU l4)
  (e : equiv-descent-data-coequalizer P (descent-data-family-cofork c Q))
  where

  equiv-double-arrow-flattening-lemma-descent-data-coequalizer :
    equiv-double-arrow
      ( double-arrow-flattening-lemma-descent-data-coequalizer P)
      ( double-arrow-flattening-lemma-coequalizer F Q c)
  pr1 equiv-double-arrow-flattening-lemma-descent-data-coequalizer =
    equiv-tot
      ( ( equiv-equiv-descent-data-coequalizer P
          ( descent-data-family-cofork c Q)
          ( e)) ∘
        ( left-map-double-arrow F))
  pr1 (pr2 equiv-double-arrow-flattening-lemma-descent-data-coequalizer) =
    equiv-tot
      ( equiv-equiv-descent-data-coequalizer P
        ( descent-data-family-cofork c Q)
        ( e))
  pr1 (pr2 (pr2 equiv-double-arrow-flattening-lemma-descent-data-coequalizer)) =
    refl-htpy
  pr2 (pr2 (pr2 equiv-double-arrow-flattening-lemma-descent-data-coequalizer)) =
    coherence-square-maps-Σ
      ( Q ∘ map-cofork c)
      ( map-equiv-descent-data-coequalizer
        ( P)
        ( descent-data-family-cofork c Q)
        ( e) ∘ left-map-double-arrow F)
      ( map-family-descent-data-coequalizer P)
      ( λ a → tr Q (coh-cofork c a))
      ( map-equiv-descent-data-coequalizer
        ( P)
        ( descent-data-family-cofork c Q)
        ( e))
      ( coherence-equiv-descent-data-coequalizer P
        ( descent-data-family-cofork c Q)
        ( e))

  equiv-cofork-equiv-double-arrow-flattening-lemma-descent-data-coequalizer :
    equiv-cofork-equiv-double-arrow
      ( cofork-flattening-lemma-descent-coequalizer c P Q e)
      ( cofork-flattening-lemma-coequalizer F Q c)
      ( equiv-double-arrow-flattening-lemma-descent-data-coequalizer)
  pr1
    equiv-cofork-equiv-double-arrow-flattening-lemma-descent-data-coequalizer =
    id-equiv
  pr1
    ( pr2
        equiv-cofork-equiv-double-arrow-flattening-lemma-descent-data-coequalizer)
    = refl-htpy
  pr2
    ( pr2
      equiv-cofork-equiv-double-arrow-flattening-lemma-descent-data-coequalizer)
    ( a , p) =
    inv
      ( ( left-whisker-concat _
          ( compute-ap-map-Σ-map-base-eq-pair-Σ
            ( map-cofork c)
            ( Q)
            ( refl)
            ( coherence-equiv-descent-data-coequalizer P
              ( descent-data-family-cofork c Q)
              ( e)
              ( a)
              ( p)))) ∙
        ( right-whisker-concat
          ( ( right-unit) ∙
            ( ap-id _) ∙
            ( triangle-eq-pair-Σ Q (coh-cofork c a) _))
          ( eq-pair-Σ refl
            ( coherence-equiv-descent-data-coequalizer P
              ( descent-data-family-cofork c Q)
              ( e)
              ( a)
              ( p)))) ∙
        ( ( left-whisker-concat-coherence-triangle-identifications'
            ( eq-pair-Σ (coh-cofork c a) refl)
            ( _)
            ( _)
            ( _)
            ( left-inv-htpy-left-whisker
              ( pair (map-cofork c (right-map-double-arrow F a)))
              ( coherence-equiv-descent-data-coequalizer P
                ( descent-data-family-cofork c Q)
                ( e)
                ( a))
              ( p))) ∙
          ( right-unit)))

  abstract
    flattening-lemma-descent-data-coequalizer :
      flattening-lemma-descent-data-coequalizer-statement c P Q e
    flattening-lemma-descent-data-coequalizer up-c =
      universal-property-coequalizer-equiv-cofork-equiv-double-arrow
        ( equiv-double-arrow-flattening-lemma-descent-data-coequalizer)
        ( equiv-cofork-equiv-double-arrow-flattening-lemma-descent-data-coequalizer)
        ( flattening-lemma-coequalizer F Q c
          ( dependent-universal-property-universal-property-coequalizer up-c))
```
