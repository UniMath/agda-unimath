# Descent data for families of equivalences over coequalizers

```agda
module synthetic-homotopy-theory.descent-data-coequalizers-equivalence-families where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-maps
open import foundation.commuting-triangles-of-maps
open import foundation.dependent-pair-types
open import foundation.double-arrows
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.homotopy-algebra
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import synthetic-homotopy-theory.coforks
open import synthetic-homotopy-theory.descent-data-coequalizers
open import synthetic-homotopy-theory.equivalences-descent-data-coequalizers
open import synthetic-homotopy-theory.families-descent-data-coequalizers
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

  family-cofork-family-with-descent-data-coequalizer-equivalence-family :
    X → UU (l4 ⊔ l5)
  family-cofork-family-with-descent-data-coequalizer-equivalence-family x =
    family-cofork-family-with-descent-data-coequalizer P x ≃
    family-cofork-family-with-descent-data-coequalizer Q x

  descent-data-coequalizer-equivalence-family :
    descent-data-coequalizer F (l4 ⊔ l5)
  pr1 descent-data-coequalizer-equivalence-family b =
    family-family-with-descent-data-coequalizer P b ≃
    family-family-with-descent-data-coequalizer Q b
  pr2 descent-data-coequalizer-equivalence-family a =
    ( equiv-postcomp-equiv
      ( equiv-family-family-with-descent-data-coequalizer Q a)
      ( family-family-with-descent-data-coequalizer P
        ( right-map-double-arrow F a))) ∘e
    ( equiv-precomp-equiv
      ( inv-equiv (equiv-family-family-with-descent-data-coequalizer P a))
      ( family-family-with-descent-data-coequalizer Q
        ( left-map-double-arrow F a)))

  equiv-equiv-descent-data-coequalizer-equivalence-family :
    (b : codomain-double-arrow F) →
    ( family-cofork-family-with-descent-data-coequalizer P (map-cofork c b) ≃
      family-cofork-family-with-descent-data-coequalizer Q (map-cofork c b)) ≃
    ( family-family-with-descent-data-coequalizer P b ≃
      family-family-with-descent-data-coequalizer Q b)
  equiv-equiv-descent-data-coequalizer-equivalence-family b =
    ( equiv-postcomp-equiv
      ( equiv-family-with-descent-data-coequalizer Q b)
      ( family-family-with-descent-data-coequalizer P b)) ∘e
    ( equiv-precomp-equiv
      ( inv-equiv (equiv-family-with-descent-data-coequalizer P b))
      ( family-cofork-family-with-descent-data-coequalizer Q (map-cofork c b)))

  equiv-descent-data-coequalizer-equivalence-family :
    equiv-descent-data-coequalizer
      ( descent-data-family-cofork c
        ( family-cofork-family-with-descent-data-coequalizer-equivalence-family))
      ( descent-data-coequalizer-equivalence-family)
  pr1 equiv-descent-data-coequalizer-equivalence-family =
    equiv-equiv-descent-data-coequalizer-equivalence-family
  pr2 equiv-descent-data-coequalizer-equivalence-family a e =
    ( ap
      ( λ f →
        ( equiv-family-with-descent-data-coequalizer Q
          ( right-map-double-arrow F a)) ∘e
        ( f) ∘e
        ( inv-equiv
          ( equiv-family-with-descent-data-coequalizer P
            ( right-map-double-arrow F a))))
      ( tr-equiv-type
        ( family-cofork-family-with-descent-data-coequalizer P)
        ( family-cofork-family-with-descent-data-coequalizer Q)
        ( coh-cofork c a)
        ( e))) ∙
    ( eq-htpy-equiv
      ( horizontal-concat-htpy
        ( coherence-family-with-descent-data-coequalizer Q a ·r map-equiv e)
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

  family-with-descent-data-coequalizer-equivalence-family :
    family-with-descent-data-coequalizer c (l4 ⊔ l5)
  pr1 family-with-descent-data-coequalizer-equivalence-family =
    family-cofork-family-with-descent-data-coequalizer-equivalence-family
  pr1 (pr2 family-with-descent-data-coequalizer-equivalence-family) =
    descent-data-coequalizer-equivalence-family
  pr2 (pr2 family-with-descent-data-coequalizer-equivalence-family) =
    equiv-descent-data-coequalizer-equivalence-family

  compute-section-family-cofork-equivalence-family :
    section-descent-data-coequalizer
      ( descent-data-coequalizer-equivalence-family) ≃
    equiv-descent-data-coequalizer
      ( descent-data-family-with-descent-data-coequalizer P)
      ( descent-data-family-with-descent-data-coequalizer Q)
  compute-section-family-cofork-equivalence-family =
    equiv-tot
      ( λ e →
        equiv-Π-equiv-family
          ( λ a →
            ( equiv-inv-htpy _ _) ∘e
            ( inv-equiv
              ( equiv-coherence-triangle-maps-inv-top'
                ( ( map-family-family-with-descent-data-coequalizer Q a) ∘
                  ( map-equiv (e (left-map-double-arrow F a))))
                ( map-equiv (e (right-map-double-arrow F a)))
                ( equiv-family-family-with-descent-data-coequalizer P a))) ∘e
            ( extensionality-equiv _ _)))
```
