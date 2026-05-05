# The flattening lemma for coequalizers

```agda
module synthetic-homotopy-theory.flattening-lemma-coequalizers where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.double-arrows
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-coproduct-types
open import foundation.universe-levels

open import synthetic-homotopy-theory.coforks
open import synthetic-homotopy-theory.dependent-universal-property-coequalizers
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

with homotopy `H : e ∘ f ~ e ∘ g`, and a type family `P : X → 𝒰` over `X`, the
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
    Σ (domain-double-arrow a) (P ∘ map-cofork a e ∘ left-map-double-arrow a) →
    Σ (codomain-double-arrow a) (P ∘ map-cofork a e)
  left-map-double-arrow-flattening-lemma-coequalizer =
    map-Σ-map-base
      ( left-map-double-arrow a)
      ( P ∘ map-cofork a e)

  right-map-double-arrow-flattening-lemma-coequalizer :
    Σ (domain-double-arrow a) (P ∘ map-cofork a e ∘ left-map-double-arrow a) →
    Σ (codomain-double-arrow a) (P ∘ map-cofork a e)
  right-map-double-arrow-flattening-lemma-coequalizer =
    map-Σ
      ( P ∘ map-cofork a e)
      ( right-map-double-arrow a)
      ( λ x → tr P (coh-cofork a e x))

  double-arrow-flattening-lemma-coequalizer : double-arrow (l1 ⊔ l4) (l2 ⊔ l4)
  double-arrow-flattening-lemma-coequalizer =
    make-double-arrow
      ( left-map-double-arrow-flattening-lemma-coequalizer)
      ( right-map-double-arrow-flattening-lemma-coequalizer)

  cofork-flattening-lemma-coequalizer :
    cofork double-arrow-flattening-lemma-coequalizer (Σ X P)
  pr1 cofork-flattening-lemma-coequalizer = map-Σ-map-base (map-cofork a e) P
  pr2 cofork-flattening-lemma-coequalizer =
    coherence-square-maps-map-Σ-map-base P
      ( right-map-double-arrow a)
      ( left-map-double-arrow a)
      ( map-cofork a e)
      ( map-cofork a e)
      ( coh-cofork a e)

  flattening-lemma-coequalizer-statement : UUω
  flattening-lemma-coequalizer-statement =
    universal-property-coequalizer a e →
    universal-property-coequalizer
      ( double-arrow-flattening-lemma-coequalizer)
      ( cofork-flattening-lemma-coequalizer)
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
    flattening-lemma-coequalizer up-e =
      universal-property-coequalizer-universal-property-pushout
        ( double-arrow-flattening-lemma-coequalizer a P e)
        ( cofork-flattening-lemma-coequalizer a P e)
        ( universal-property-pushout-bottom-universal-property-pushout-top-cube-equiv
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
          ( right-distributive-Σ-coproduct
            ( ( P) ∘
              ( horizontal-map-cocone-cofork a e) ∘
              ( vertical-map-span-cocone-cofork a)))
          ( id-equiv)
          ( id-equiv)
          ( id-equiv)
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
          ( flattening-lemma-pushout P
            ( vertical-map-span-cocone-cofork a)
            ( horizontal-map-span-cocone-cofork a)
            ( cocone-codiagonal-cofork a e)
            ( universal-property-pushout-universal-property-coequalizer a e
              ( up-e))))
```
