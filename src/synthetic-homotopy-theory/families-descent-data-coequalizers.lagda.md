# Families with descent data for coequalizers

```agda
module synthetic-homotopy-theory.families-descent-data-coequalizers where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-maps
open import foundation.dependent-pair-types
open import foundation.double-arrows
open import foundation.equivalences
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import synthetic-homotopy-theory.coforks
open import synthetic-homotopy-theory.descent-data-coequalizers
open import synthetic-homotopy-theory.equivalences-descent-data-coequalizers
```

</details>

## Idea

## Definitions

### Type families over a cofork equipped with corresponding descent data for coequalizers

```agda
module _
  {l1 l2 l3 : Level} {F : double-arrow l1 l2}
  {X : UU l3} (c : cofork F X)
  where

  family-with-descent-data-coequalizer :
    (l4 : Level) → UU (l1 ⊔ l2 ⊔ l3 ⊔ lsuc l4)
  family-with-descent-data-coequalizer l4 =
    Σ ( X → UU l4)
      ( λ P →
        Σ ( descent-data-coequalizer F l4)
          ( λ Q →
            equiv-descent-data-coequalizer
              ( descent-data-family-cofork c P)
              ( Q)))
```

### Components of a type family with corresponding descent data

```agda
module _
  {l1 l2 l3 l4 : Level} {F : double-arrow l1 l2}
  {X : UU l3} {c : cofork F X}
  (P : family-with-descent-data-coequalizer c l4)
  where

  family-cofork-family-with-descent-data-coequalizer : X → UU l4
  family-cofork-family-with-descent-data-coequalizer = pr1 P

  descent-data-family-with-descent-data-coequalizer :
    descent-data-coequalizer F l4
  descent-data-family-with-descent-data-coequalizer = pr1 (pr2 P)

  family-family-with-descent-data-coequalizer :
    codomain-double-arrow F → UU l4
  family-family-with-descent-data-coequalizer =
    family-descent-data-coequalizer
      ( descent-data-family-with-descent-data-coequalizer)

  equiv-family-family-with-descent-data-coequalizer :
    (a : domain-double-arrow F) →
    family-family-with-descent-data-coequalizer (left-map-double-arrow F a) ≃
    family-family-with-descent-data-coequalizer (right-map-double-arrow F a)
  equiv-family-family-with-descent-data-coequalizer =
    equiv-family-descent-data-coequalizer
      ( descent-data-family-with-descent-data-coequalizer)

  map-family-family-with-descent-data-coequalizer :
    (a : domain-double-arrow F) →
    family-family-with-descent-data-coequalizer (left-map-double-arrow F a) →
    family-family-with-descent-data-coequalizer (right-map-double-arrow F a)
  map-family-family-with-descent-data-coequalizer =
    map-family-descent-data-coequalizer
      ( descent-data-family-with-descent-data-coequalizer)

  equiv-descent-data-family-with-descent-data-coequalizer :
    equiv-descent-data-coequalizer
      ( descent-data-family-cofork c
        ( family-cofork-family-with-descent-data-coequalizer))
      ( descent-data-family-with-descent-data-coequalizer)
  equiv-descent-data-family-with-descent-data-coequalizer = pr2 (pr2 P)

  equiv-family-with-descent-data-coequalizer :
    (a : codomain-double-arrow F) →
    family-cofork-family-with-descent-data-coequalizer (map-cofork c a) ≃
    family-family-with-descent-data-coequalizer a
  equiv-family-with-descent-data-coequalizer =
    equiv-equiv-descent-data-coequalizer
      ( descent-data-family-cofork c
        ( family-cofork-family-with-descent-data-coequalizer))
      ( descent-data-family-with-descent-data-coequalizer)
      ( equiv-descent-data-family-with-descent-data-coequalizer)

  map-family-with-descent-data-coequalizer :
    (a : codomain-double-arrow F) →
    family-cofork-family-with-descent-data-coequalizer (map-cofork c a) →
    family-family-with-descent-data-coequalizer a
  map-family-with-descent-data-coequalizer =
    map-equiv-descent-data-coequalizer
      ( descent-data-family-cofork c
        ( family-cofork-family-with-descent-data-coequalizer))
      ( descent-data-family-with-descent-data-coequalizer)
      ( equiv-descent-data-family-with-descent-data-coequalizer)

  is-equiv-map-family-with-descent-data-coequalizer :
    (a : codomain-double-arrow F) →
    is-equiv (map-family-with-descent-data-coequalizer a)
  is-equiv-map-family-with-descent-data-coequalizer =
    is-equiv-map-equiv-descent-data-coequalizer
      ( descent-data-family-cofork c
        ( family-cofork-family-with-descent-data-coequalizer))
      ( descent-data-family-with-descent-data-coequalizer)
      ( equiv-descent-data-family-with-descent-data-coequalizer)

  coherence-family-with-descent-data-coequalizer :
    (a : domain-double-arrow F) →
    coherence-square-maps
      ( map-family-with-descent-data-coequalizer (left-map-double-arrow F a))
      ( tr
        ( family-cofork-family-with-descent-data-coequalizer)
        ( coh-cofork c a))
      ( map-family-family-with-descent-data-coequalizer a)
      ( map-family-with-descent-data-coequalizer (right-map-double-arrow F a))
  coherence-family-with-descent-data-coequalizer =
    coherence-equiv-descent-data-coequalizer
      ( descent-data-family-cofork c
        ( family-cofork-family-with-descent-data-coequalizer))
      ( descent-data-family-with-descent-data-coequalizer)
      ( equiv-descent-data-family-with-descent-data-coequalizer)
```
