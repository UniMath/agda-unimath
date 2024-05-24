# Descent data for families of functions over coequalizers

```agda
module synthetic-homotopy-theory.descent-data-coequalizers-function-families where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-maps
open import foundation.commuting-triangles-of-maps
open import foundation.dependent-pair-types
open import foundation.double-arrows
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.homotopy-algebra
open import foundation.identity-types
open import foundation.postcomposition-functions
open import foundation.transport-along-identifications
open import foundation.universal-property-equivalences
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import synthetic-homotopy-theory.coforks
open import synthetic-homotopy-theory.descent-data-coequalizers
open import synthetic-homotopy-theory.equivalences-descent-data-coequalizers
open import synthetic-homotopy-theory.families-descent-data-coequalizers
open import synthetic-homotopy-theory.morphisms-descent-data-coequalizers
open import synthetic-homotopy-theory.sections-descent-data-coequalizers
```

</details>

## Idea

## Definitions

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {F : double-arrow l1 l2}
  {X : UU l3} {c : cofork F X}
  (P : family-with-descent-data-coequalizer c l4)
  (Q : family-with-descent-data-coequalizer c l5)
  where

  family-cofork-family-with-descent-data-coequalizer-function-family :
    X → UU (l4 ⊔ l5)
  family-cofork-family-with-descent-data-coequalizer-function-family x =
    family-cofork-family-with-descent-data-coequalizer P x →
    family-cofork-family-with-descent-data-coequalizer Q x

  descent-data-coequalizer-function-family :
    descent-data-coequalizer F (l4 ⊔ l5)
  pr1 descent-data-coequalizer-function-family b =
    family-family-with-descent-data-coequalizer P b →
    family-family-with-descent-data-coequalizer Q b
  pr2 descent-data-coequalizer-function-family a =
    ( equiv-postcomp
      ( family-family-with-descent-data-coequalizer P
        ( right-map-double-arrow F a))
      ( equiv-family-family-with-descent-data-coequalizer Q a)) ∘e
    ( equiv-precomp
      ( inv-equiv (equiv-family-family-with-descent-data-coequalizer P a))
      ( family-family-with-descent-data-coequalizer Q
        ( left-map-double-arrow F a)))

  equiv-equiv-descent-data-coequalizer-function-family :
    (b : codomain-double-arrow F) →
    ( family-cofork-family-with-descent-data-coequalizer P (map-cofork c b) →
      family-cofork-family-with-descent-data-coequalizer Q (map-cofork c b)) ≃
    ( family-family-with-descent-data-coequalizer P b →
      family-family-with-descent-data-coequalizer Q b)
  equiv-equiv-descent-data-coequalizer-function-family b =
    ( equiv-postcomp
      ( family-family-with-descent-data-coequalizer P b)
      ( equiv-family-with-descent-data-coequalizer Q b)) ∘e
    ( equiv-precomp
      ( inv-equiv (equiv-family-with-descent-data-coequalizer P b))
      ( family-cofork-family-with-descent-data-coequalizer Q (map-cofork c b)))

  equiv-descent-data-coequalizer-function-family :
    equiv-descent-data-coequalizer
      ( descent-data-family-cofork c
        ( family-cofork-family-with-descent-data-coequalizer-function-family))
      ( descent-data-coequalizer-function-family)
  pr1 equiv-descent-data-coequalizer-function-family =
    equiv-equiv-descent-data-coequalizer-function-family
  pr2 equiv-descent-data-coequalizer-function-family a f =
    ( ap
      ( λ g →
        ( map-family-with-descent-data-coequalizer Q
          ( right-map-double-arrow F a)) ∘
        ( g) ∘
        ( map-inv-equiv
          ( equiv-family-with-descent-data-coequalizer P
            ( right-map-double-arrow F a))))
      ( tr-function-type
        ( family-cofork-family-with-descent-data-coequalizer P)
        ( family-cofork-family-with-descent-data-coequalizer Q)
        ( coh-cofork c a)
        ( f))) ∙
    ( eq-htpy
      ( horizontal-concat-htpy
        ( coherence-family-with-descent-data-coequalizer Q a ·r f)
        ( coherence-square-maps-inv-equiv
          ( equiv-tr
            ( family-cofork-family-with-descent-data-coequalizer P)
            ( coh-cofork c a))
          ( equiv-family-with-descent-data-coequalizer P
            ( left-map-double-arrow F a))
          ( equiv-family-with-descent-data-coequalizer P
            ( right-map-double-arrow F a))
          ( equiv-family-family-with-descent-data-coequalizer P a)
          ( inv-htpy (coherence-family-with-descent-data-coequalizer P a)))))

  family-with-descent-data-coequalizer-function-family :
    family-with-descent-data-coequalizer c (l4 ⊔ l5)
  pr1 family-with-descent-data-coequalizer-function-family =
    family-cofork-family-with-descent-data-coequalizer-function-family
  pr1 (pr2 family-with-descent-data-coequalizer-function-family) =
    descent-data-coequalizer-function-family
  pr2 (pr2 family-with-descent-data-coequalizer-function-family) =
    equiv-descent-data-coequalizer-function-family

  compute-section-family-cofork-function-family :
    section-descent-data-coequalizer descent-data-coequalizer-function-family ≃
    hom-descent-data-coequalizer
      ( descent-data-family-with-descent-data-coequalizer P)
      ( descent-data-family-with-descent-data-coequalizer Q)
  compute-section-family-cofork-function-family =
    equiv-tot
      ( λ h →
        equiv-Π-equiv-family
          ( λ a →
            ( equiv-inv-htpy _ _) ∘e
            ( inv-equiv
              ( equiv-coherence-triangle-maps-inv-top'
                ( ( map-family-family-with-descent-data-coequalizer Q a) ∘
                  ( h (left-map-double-arrow F a)))
                ( h (right-map-double-arrow F a))
                ( equiv-family-family-with-descent-data-coequalizer P a))) ∘e
            ( equiv-funext)))
```
