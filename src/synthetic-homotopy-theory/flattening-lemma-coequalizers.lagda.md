# The flattening lemma for coequalizers

```agda
{-# OPTIONS --cubical-compatible #-}

module synthetic-homotopy-theory.flattening-lemma-coequalizers where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
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

The **flattening lemma** for
[coequalizers](synthetic-homotopy-theory.coequalizers.md) states that
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
  { l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} (f g : A → B) {X : UU l3}
  ( P : X → UU l4) (e : cofork f g X)
  where

  bottom-map-cofork-flattening-lemma-coequalizer :
    Σ A (P ∘ map-cofork f g e ∘ f) → Σ B (P ∘ map-cofork f g e)
  bottom-map-cofork-flattening-lemma-coequalizer =
    map-Σ-map-base f (P ∘ map-cofork f g e)

  top-map-cofork-flattening-lemma-coequalizer :
    Σ A (P ∘ map-cofork f g e ∘ f) → Σ B (P ∘ map-cofork f g e)
  top-map-cofork-flattening-lemma-coequalizer =
    map-Σ (P ∘ map-cofork f g e) g (λ a → tr P (coherence-cofork f g e a))

  cofork-flattening-lemma-coequalizer :
    cofork
      ( bottom-map-cofork-flattening-lemma-coequalizer)
      ( top-map-cofork-flattening-lemma-coequalizer)
      ( Σ X P)
  pr1 cofork-flattening-lemma-coequalizer = map-Σ-map-base (map-cofork f g e) P
  pr2 cofork-flattening-lemma-coequalizer =
    coherence-square-maps-map-Σ-map-base P g f
      ( map-cofork f g e)
      ( map-cofork f g e)
      ( coherence-cofork f g e)

  flattening-lemma-coequalizer-statement : UUω
  flattening-lemma-coequalizer-statement =
    ( {l : Level} → dependent-universal-property-coequalizer l f g e) →
    { l : Level} →
    universal-property-coequalizer l
      ( bottom-map-cofork-flattening-lemma-coequalizer)
      ( top-map-cofork-flattening-lemma-coequalizer)
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
  { l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} (f g : A → B) {X : UU l3}
  ( P : X → UU l4) (e : cofork f g X)
  where

  abstract
    flattening-lemma-coequalizer :
      flattening-lemma-coequalizer-statement f g P e
    flattening-lemma-coequalizer dup-coequalizer =
      universal-property-coequalizer-universal-property-pushout
        ( bottom-map-cofork-flattening-lemma-coequalizer f g P e)
        ( top-map-cofork-flattening-lemma-coequalizer f g P e)
        ( cofork-flattening-lemma-coequalizer f g P e)
        ( universal-property-pushout-bottom-universal-property-pushout-top-cube-is-equiv
          ( vertical-map-span-cocone-cofork
            ( bottom-map-cofork-flattening-lemma-coequalizer f g P e)
            ( top-map-cofork-flattening-lemma-coequalizer f g P e))
          ( horizontal-map-span-cocone-cofork
            ( bottom-map-cofork-flattening-lemma-coequalizer f g P e)
            ( top-map-cofork-flattening-lemma-coequalizer f g P e))
          ( horizontal-map-cocone-flattening-pushout P
            ( vertical-map-span-cocone-cofork f g)
            ( horizontal-map-span-cocone-cofork f g)
            ( cocone-codiagonal-cofork f g e))
          ( vertical-map-cocone-flattening-pushout P
            ( vertical-map-span-cocone-cofork f g)
            ( horizontal-map-span-cocone-cofork f g)
            ( cocone-codiagonal-cofork f g e))
          ( vertical-map-span-flattening-pushout P
            ( vertical-map-span-cocone-cofork f g)
            ( horizontal-map-span-cocone-cofork f g)
            ( cocone-codiagonal-cofork f g e))
          ( horizontal-map-span-flattening-pushout P
            ( vertical-map-span-cocone-cofork f g)
            ( horizontal-map-span-cocone-cofork f g)
            ( cocone-codiagonal-cofork f g e))
          ( horizontal-map-cocone-flattening-pushout P
            ( vertical-map-span-cocone-cofork f g)
            ( horizontal-map-span-cocone-cofork f g)
            ( cocone-codiagonal-cofork f g e))
          ( vertical-map-cocone-flattening-pushout P
            ( vertical-map-span-cocone-cofork f g)
            ( horizontal-map-span-cocone-cofork f g)
            ( cocone-codiagonal-cofork f g e))
          ( map-equiv
            ( right-distributive-Σ-coprod A A
              ( ( P) ∘
                ( horizontal-map-cocone-cofork f g e) ∘
                ( vertical-map-span-cocone-cofork f g))))
          ( id)
          ( id)
          ( id)
          ( coherence-square-cocone-flattening-pushout P
            ( vertical-map-span-cocone-cofork f g)
            ( horizontal-map-span-cocone-cofork f g)
            ( cocone-codiagonal-cofork f g e))
          ( λ where
            (inl a , t) → refl
            (inr a , t) → refl)
          ( λ where
            (inl a , t) → refl
            (inr a , t) → refl)
          ( refl-htpy)
          ( refl-htpy)
          ( coherence-square-cocone-cofork
            ( bottom-map-cofork-flattening-lemma-coequalizer f g P e)
            ( top-map-cofork-flattening-lemma-coequalizer f g P e)
            ( cofork-flattening-lemma-coequalizer f g P e))
          ( λ where
            (inl a , t) → refl
            (inr a , t) →
              ( ap-id
                ( eq-pair-Σ
                  ( coherence-cofork f g e a)
                  ( refl))) ∙
              ( inv right-unit))
          ( is-equiv-map-equiv
            ( right-distributive-Σ-coprod A A
              ( ( P) ∘
                ( horizontal-map-cocone-cofork f g e) ∘
                ( vertical-map-span-cocone-cofork f g))))
          ( is-equiv-id)
          ( is-equiv-id)
          ( is-equiv-id)
          ( flattening-lemma-pushout P
            ( vertical-map-span-cocone-cofork f g)
            ( horizontal-map-span-cocone-cofork f g)
            ( cocone-codiagonal-cofork f g e)
            ( dependent-universal-property-pushout-dependent-universal-property-coequalizer
              ( f)
              ( g)
              ( e)
              ( dup-coequalizer))))
```
