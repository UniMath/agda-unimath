# Sections of descent data for coequalizers

```agda
module synthetic-homotopy-theory.sections-descent-data-coequalizers where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.commuting-triangles-of-maps
open import foundation.dependent-pair-types
open import foundation.double-arrows
open import foundation.embeddings
open import foundation.equivalences
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import synthetic-homotopy-theory.coforks
open import synthetic-homotopy-theory.dependent-coforks
open import synthetic-homotopy-theory.dependent-universal-property-coequalizers
open import synthetic-homotopy-theory.descent-data-coequalizers
open import synthetic-homotopy-theory.families-descent-data-coequalizers
open import synthetic-homotopy-theory.universal-property-coequalizers
```

</details>

## Idea

## Definitions

```agda
module _
  {l1 l2 l3 : Level} {F : double-arrow l1 l2}
  (P : descent-data-coequalizer F l3)
  where

  section-descent-data-coequalizer : UU (l1 ⊔ l2 ⊔ l3)
  section-descent-data-coequalizer =
    Σ ( (b : codomain-double-arrow F) → family-descent-data-coequalizer P b)
      ( λ s →
        (a : domain-double-arrow F) →
        map-family-descent-data-coequalizer P a
          ( s (left-map-double-arrow F a)) ＝
        s (right-map-double-arrow F a))
```

## Properties

### Sections of families over a coequalizer correspond to sections of the corresponding descent data

```agda
module _
  {l1 l2 l3 l4 : Level} {F : double-arrow l1 l2}
  {X : UU l3} {c : cofork F X}
  (P : family-with-descent-data-coequalizer c l4)
  where

  section-descent-data-section-family-cofork :
    ((x : X) → family-cofork-family-with-descent-data-coequalizer P x) →
    section-descent-data-coequalizer
      ( descent-data-family-with-descent-data-coequalizer P)
  pr1 (section-descent-data-section-family-cofork f) b =
    map-family-with-descent-data-coequalizer P b (f (map-cofork c b))
  pr2 (section-descent-data-section-family-cofork f) a =
    ( inv
      ( coherence-family-with-descent-data-coequalizer P a
        ( f (map-cofork c (left-map-double-arrow F a))))) ∙
    ( ap
      ( map-family-with-descent-data-coequalizer P (right-map-double-arrow F a))
      ( apd f (coh-cofork c a)))

  equiv-section-descent-data-dependent-cofork :
    dependent-cofork c
      ( family-cofork-family-with-descent-data-coequalizer P) ≃
    section-descent-data-coequalizer
      ( descent-data-family-with-descent-data-coequalizer P)
  equiv-section-descent-data-dependent-cofork =
    equiv-Σ _
      ( equiv-Π-equiv-family (equiv-family-with-descent-data-coequalizer P))
      ( λ s →
        equiv-Π-equiv-family
          ( λ a →
            ( equiv-inv-concat
              ( coherence-family-with-descent-data-coequalizer P a
                ( s (left-map-double-arrow F a)))
              ( _)) ∘e
            ( equiv-ap-emb
              ( emb-equiv
                ( equiv-family-with-descent-data-coequalizer P
                  ( right-map-double-arrow F a))))))

  triangle-section-descent-data-dependent-cofork :
    coherence-triangle-maps
      ( section-descent-data-section-family-cofork)
      ( map-equiv equiv-section-descent-data-dependent-cofork)
      ( dependent-cofork-map c)
  triangle-section-descent-data-dependent-cofork = refl-htpy

  is-equiv-section-descent-data-section-family-cofork :
    universal-property-coequalizer c →
    is-equiv (section-descent-data-section-family-cofork)
  is-equiv-section-descent-data-section-family-cofork up-c =
    is-equiv-left-map-triangle
      ( section-descent-data-section-family-cofork)
      ( map-equiv equiv-section-descent-data-dependent-cofork)
      ( dependent-cofork-map c)
      ( triangle-section-descent-data-dependent-cofork)
      ( dependent-universal-property-universal-property-coequalizer up-c
        ( family-cofork-family-with-descent-data-coequalizer P))
      ( is-equiv-map-equiv equiv-section-descent-data-dependent-cofork)

  compute-section-family-cofork :
    universal-property-coequalizer c →
    ((x : X) → family-cofork-family-with-descent-data-coequalizer P x) ≃
    section-descent-data-coequalizer
      ( descent-data-family-with-descent-data-coequalizer P)
  pr1 (compute-section-family-cofork _) =
    section-descent-data-section-family-cofork
  pr2 (compute-section-family-cofork up-c) =
    is-equiv-section-descent-data-section-family-cofork up-c
```
