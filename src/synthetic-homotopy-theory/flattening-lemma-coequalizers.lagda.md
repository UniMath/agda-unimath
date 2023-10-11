# The flattening lemma for coequalizers

```agda
module synthetic-homotopy-theory.flattening-lemma-coequalizers where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-triangles-of-maps
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universal-property-dependent-pair-types
open import foundation.universe-levels

open import synthetic-homotopy-theory.coforks
open import synthetic-homotopy-theory.dependent-coforks
open import synthetic-homotopy-theory.dependent-universal-property-coequalizers
open import synthetic-homotopy-theory.universal-property-coequalizers
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

The proof is analogous to the one of the
[flattening lemma for pushouts](synthetic-homotopy-theory.flattening-lemma-pushouts.md).

```agda
module _
  { l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} (f g : A → B) {X : UU l3}
  ( P : X → UU l4) (e : cofork f g X)
  where

  cofork-map-flattening-coequalizer :
    { l : Level} (Y : UU l) →
    ( Σ X P → Y) →
    cofork
      ( bottom-map-cofork-flattening-lemma-coequalizer f g P e)
      ( top-map-cofork-flattening-lemma-coequalizer f g P e)
      ( Y)
  cofork-map-flattening-coequalizer Y =
    cofork-map
      ( bottom-map-cofork-flattening-lemma-coequalizer f g P e)
      ( top-map-cofork-flattening-lemma-coequalizer f g P e)
      ( cofork-flattening-lemma-coequalizer f g P e)

  comparison-dependent-cofork-ind-Σ-cofork :
    { l : Level} (Y : UU l) →
    Σ ( (b : B) → P (map-cofork f g e b) → Y)
      ( λ k →
        ( a : A) (t : P (map-cofork f g e (f a))) →
        ( k (f a) t) ＝
        ( k (g a) (tr P (coherence-cofork f g e a) t))) ≃
    dependent-cofork f g e (λ x → P x → Y)
  comparison-dependent-cofork-ind-Σ-cofork Y =
    equiv-tot
      ( λ k →
        equiv-Π-equiv-family
          ( equiv-htpy-dependent-function-dependent-identification-function-type
            ( Y)
            ( coherence-cofork f g e)
            ( k ∘ f)
            ( k ∘ g)))

  triangle-comparison-dependent-cofork-ind-Σ-cofork :
    { l : Level} (Y : UU l) →
    coherence-triangle-maps
      ( dependent-cofork-map f g e {P = (λ x → P x → Y)})
      ( map-equiv (comparison-dependent-cofork-ind-Σ-cofork Y))
      ( map-equiv equiv-ev-pair² ∘ cofork-map-flattening-coequalizer Y ∘ ind-Σ)
  triangle-comparison-dependent-cofork-ind-Σ-cofork Y h =
    eq-pair-Σ
      ( refl)
      ( eq-htpy
        ( inv-htpy
          ( compute-equiv-htpy-dependent-function-dependent-identification-function-type
            ( Y)
            ( coherence-cofork f g e)
            ( h))))

  flattening-lemma-coequalizer :
    flattening-lemma-coequalizer-statement f g P e
  flattening-lemma-coequalizer dup-coequalizer Y =
    is-equiv-left-factor
      ( cofork-map-flattening-coequalizer Y)
      ( ind-Σ)
      ( is-equiv-right-factor
        ( map-equiv equiv-ev-pair²)
        ( cofork-map-flattening-coequalizer Y ∘ ind-Σ)
        ( is-equiv-map-equiv equiv-ev-pair²)
        ( is-equiv-right-factor-htpy
          ( dependent-cofork-map f g e {P = (λ x → P x → Y)})
          ( map-equiv (comparison-dependent-cofork-ind-Σ-cofork Y))
          ( ( map-equiv equiv-ev-pair²) ∘
            ( cofork-map-flattening-coequalizer Y) ∘
            ( ind-Σ))
          ( triangle-comparison-dependent-cofork-ind-Σ-cofork Y)
          ( is-equiv-map-equiv (comparison-dependent-cofork-ind-Σ-cofork Y))
          ( dup-coequalizer (λ x → P x → Y))))
      ( is-equiv-ind-Σ)
```
