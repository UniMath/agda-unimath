# Descent data for type families of function types over sequential colimits

```agda
{-# OPTIONS --lossy-unification --allow-unsolved-metas #-}

module synthetic-homotopy-theory.descent-data-function-types-over-sequential-colimits where
```

<details><summary>Imports</summary>

```agda
-- open import foundation.commuting-squares-of-maps
-- open import foundation.commuting-triangles-of-maps
-- open import foundation.contractible-maps
-- open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
-- open import foundation.fibers-of-maps
-- open import foundation.function-extensionality
-- open import foundation.function-types
-- open import foundation.functoriality-dependent-function-types
-- open import foundation.functoriality-dependent-pair-types
-- open import foundation.homotopies
-- open import foundation.homotopy-algebra
open import foundation.postcomposition-functions
-- open import foundation.transport-along-identifications
open import foundation.universal-property-equivalences
open import foundation.universe-levels
-- open import foundation.whiskering-homotopies-composition

open import synthetic-homotopy-theory.cocones-under-sequential-diagrams
open import synthetic-homotopy-theory.descent-data-sequential-colimits
-- open import synthetic-homotopy-theory.equivalences-descent-data-pushouts
open import synthetic-homotopy-theory.families-descent-data-sequential-colimits
-- open import synthetic-homotopy-theory.morphisms-descent-data-pushouts
-- open import synthetic-homotopy-theory.sections-descent-data-pushouts
open import synthetic-homotopy-theory.sequential-diagrams
-- open import synthetic-homotopy-theory.universal-property-pushouts
```

## Idea

## Definitions

### TODO

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {A : sequential-diagram l1}
  {X : UU l3} {c : cocone-sequential-diagram A X}
  (P : family-with-descent-data-sequential-colimit c l4)
  (Q : family-with-descent-data-sequential-colimit c l5)
  where

  family-cocone-function-type-sequential-colimit : X → UU (l4 ⊔ l5)
  family-cocone-function-type-sequential-colimit x =
    family-cocone-family-with-descent-data-sequential-colimit P x →
    family-cocone-family-with-descent-data-sequential-colimit Q x

  descent-data-function-type-sequential-colimit :
    descent-data-sequential-colimit A (l4 ⊔ l5)
  pr1 descent-data-function-type-sequential-colimit n a =
    family-family-with-descent-data-sequential-colimit P n a →
    family-family-with-descent-data-sequential-colimit Q n a
  pr2 descent-data-function-type-sequential-colimit n a =
    ( equiv-postcomp _
      ( equiv-family-family-with-descent-data-sequential-colimit Q n a)) ∘e
    ( equiv-precomp
      ( inv-equiv (equiv-family-family-with-descent-data-sequential-colimit P n a))
      ( _))
```

## Properties

```agda
module _
  {l1 l2 l3 l4 : Level} {A : sequential-diagram l1}
  {X : UU l2} {c : cocone-sequential-diagram A X}
  (P : family-with-descent-data-sequential-colimit c l3)
  (Q : family-with-descent-data-sequential-colimit c l4)
  where

  equiv-hom-descent-data-map-family-cocone-sequential-diagram :
    ( (x : X) →
      family-cocone-family-with-descent-data-sequential-colimit P x →
      family-cocone-family-with-descent-data-sequential-colimit Q x) ≃
    ( hom-descent-data-sequential-colimit
      ( descent-data-family-with-descent-data-sequential-colimit P)
      ( descent-data-family-with-descent-data-sequential-colimit Q))
  equiv-hom-descent-data-map-family-cocone-sequential-diagram = {!!}
```
