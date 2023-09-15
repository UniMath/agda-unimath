# The flattening lemma for pushouts

```agda
module synthetic-homotopy-theory.flattening-lemma-pushouts where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-maps
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

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.dependent-cocones-under-spans
open import synthetic-homotopy-theory.dependent-universal-property-pushouts
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

## Idea

The **flattening lemma** for [pushouts](synthetic-homotopy-theory.pushouts.md)
states that pushouts commute with
[dependent pair types](foundation.dependent-pair-types.md). More precisely,
given a pushout square

```text
      g
  S -----> B
  |        |
 f|        |j
  V        V
  A -----> X
      i
```

with homotopy `H : i ∘ f ~ j ∘ g`, and for any type family `P` over `X`, the
commuting square

```text
  Σ (s : S), P(if(s)) ---> Σ (s : S), P(jg(s)) ---> Σ (b : B), P(j(b))
           |                                                 |
           |                                                 |
           V                                                 V
  Σ (a : A), P(i(a)) -----------------------------> Σ (x : X), P(x)
```

is again a pushout square.

## Definitions

### The statement of the flattening lemma for pushouts

```agda
module _
  { l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  { X : UU l4} (P : X → UU l5)
  ( f : S → A) (g : S → B) (c : cocone f g X)
  ( dup-pushout : {l : Level} → dependent-universal-property-pushout l f g c)
  where

  horizontal-map-cocone-flattening-pushout :
    Σ A (P ∘ horizontal-map-cocone f g c) → Σ X P
  horizontal-map-cocone-flattening-pushout =
    map-Σ-map-base (horizontal-map-cocone f g c) P

  vertical-map-cocone-flattening-pushout :
    Σ B (P ∘ vertical-map-cocone f g c) → Σ X P
  vertical-map-cocone-flattening-pushout =
    map-Σ-map-base (vertical-map-cocone f g c) P

  coherence-square-cocone-flattening-pushout :
    coherence-square-maps
      ( map-Σ
        ( P ∘ vertical-map-cocone f g c)
        ( g)
        ( λ s → tr P (coherence-square-cocone f g c s)))
      ( map-Σ-map-base f (P ∘ horizontal-map-cocone f g c))
      ( vertical-map-cocone-flattening-pushout)
      ( horizontal-map-cocone-flattening-pushout)
  coherence-square-cocone-flattening-pushout =
    coherence-square-maps-map-Σ-map-base P g f
      ( vertical-map-cocone f g c)
      ( horizontal-map-cocone f g c)
      ( coherence-square-cocone f g c)

  cocone-flattening-pushout :
    cocone
      ( map-Σ-map-base f (P ∘ horizontal-map-cocone f g c))
      ( map-Σ
        ( P ∘ vertical-map-cocone f g c)
        ( g)
        ( λ s → tr P (coherence-square-cocone f g c s)))
      ( Σ X P)
  pr1 cocone-flattening-pushout =
    horizontal-map-cocone-flattening-pushout
  pr1 (pr2 cocone-flattening-pushout) =
    vertical-map-cocone-flattening-pushout
  pr2 (pr2 cocone-flattening-pushout) =
    coherence-square-cocone-flattening-pushout

  flattening-lemma-pushout-statement : UUω
  flattening-lemma-pushout-statement =
    { l : Level} →
    universal-property-pushout l
      ( map-Σ-map-base f (P ∘ horizontal-map-cocone f g c))
      ( map-Σ
        ( P ∘ vertical-map-cocone f g c)
        ( g)
        ( λ s → tr P (coherence-square-cocone f g c s)))
      ( cocone-flattening-pushout)
```

## Properties

### Proof of the flattening lemma for pushouts

The proof uses the theorem that maps from sigma types are equivalent to
dependent maps over the index type, for which we can invoke the dependent
universal property of the indexing pushout.

```agda
module _
  { l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  { X : UU l4} (P : X → UU l5)
  ( f : S → A) (g : S → B) (c : cocone f g X)
  ( dup-pushout : {l : Level} → dependent-universal-property-pushout l f g c)
  where

  cocone-map-flattening-pushout :
    { l : Level} (Y : UU l) →
    ( Σ X P → Y) →
    cocone
      ( map-Σ-map-base f (P ∘ horizontal-map-cocone f g c))
      ( map-Σ
        ( P ∘ vertical-map-cocone f g c)
        ( g)
        ( λ s → tr P (coherence-square-cocone f g c s)))
      ( Y)
  cocone-map-flattening-pushout Y =
    cocone-map
      ( map-Σ-map-base f (P ∘ horizontal-map-cocone f g c))
      ( map-Σ
        ( P ∘ vertical-map-cocone f g c)
        ( g)
        ( λ s → tr P (coherence-square-cocone f g c s)))
      ( cocone-flattening-pushout P f g c dup-pushout)

  comparison-dependent-cocone-ind-Σ-cocone :
    { l : Level} (Y : UU l) →
    Σ ( (a : A) → P (horizontal-map-cocone f g c a) → Y)
      ( λ k →
        Σ ( (b : B) → P (vertical-map-cocone f g c b) → Y)
          ( λ l →
            ( s : S) (t : P (horizontal-map-cocone f g c (f s))) →
            ( k (f s) t) ＝
            ( l (g s) (tr P (coherence-square-cocone f g c s) t)))) ≃
    dependent-cocone f g c (λ x → P x → Y)
  comparison-dependent-cocone-ind-Σ-cocone Y =
    equiv-tot
      ( λ k →
        equiv-tot
          ( λ l →
            equiv-Π-equiv-family
              ( equiv-htpy-dependent-fuction-dependent-identification-function-type
                ( Y)
                ( coherence-square-cocone f g c)
                ( k ∘ f)
                ( l ∘ g))))

  triangle-comparison-dependent-cocone-ind-Σ-cocone :
    { l : Level} (Y : UU l) →
    coherence-triangle-maps
      ( dependent-cocone-map f g c (λ x → P x → Y))
      ( map-equiv (comparison-dependent-cocone-ind-Σ-cocone Y))
      ( map-equiv equiv-ev-pair³ ∘ cocone-map-flattening-pushout Y ∘ ind-Σ)
  triangle-comparison-dependent-cocone-ind-Σ-cocone Y h =
    eq-pair-Σ
      ( refl)
      ( eq-pair-Σ
        ( refl)
        ( eq-htpy
          ( inv-htpy
            ( compute-equiv-htpy-dependent-fuction-dependent-identification-function-type
              ( Y)
              ( coherence-square-cocone f g c)
              ( h)))))

  flattening-lemma-pushout :
    flattening-lemma-pushout-statement P f g c dup-pushout
  flattening-lemma-pushout Y =
    is-equiv-left-factor
      ( cocone-map-flattening-pushout Y)
      ( ind-Σ)
      ( is-equiv-right-factor
        ( map-equiv equiv-ev-pair³)
        ( cocone-map-flattening-pushout Y ∘ ind-Σ)
        ( is-equiv-map-equiv equiv-ev-pair³)
        ( is-equiv-right-factor-htpy
          ( dependent-cocone-map f g c (λ x → P x → Y))
          ( map-equiv (comparison-dependent-cocone-ind-Σ-cocone Y))
          ( map-equiv equiv-ev-pair³ ∘ cocone-map-flattening-pushout Y ∘ ind-Σ)
          ( triangle-comparison-dependent-cocone-ind-Σ-cocone Y)
          ( is-equiv-map-equiv (comparison-dependent-cocone-ind-Σ-cocone Y))
          ( dup-pushout (λ x → P x → Y))))
      ( is-equiv-ind-Σ)
```
