# Descent data for sequential colimits

```agda
module synthetic-homotopy-theory.descent-data-sequential-colimits where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-sequential-diagrams
open import synthetic-homotopy-theory.dependent-sequential-diagrams
open import synthetic-homotopy-theory.equifibered-sequential-diagrams
open import synthetic-homotopy-theory.equivalences-dependent-sequential-diagrams
open import synthetic-homotopy-theory.morphisms-dependent-sequential-diagrams
open import synthetic-homotopy-theory.sequential-diagrams
```

</details>

## Idea

Given a [sequential diagram](synthetic-homotopy-theory.sequential-diagrams.md)
`(A, a)`, we may ask how to construct type families over its
[sequential colimit](synthetic-homotopy-theory.universal-property-sequential-colimits.md).

The data required to construct a type family is called
{{#concept "descent data" Disambiguation="sequential colimits" Agda=descent-data-sequential-colimit}}
for sequential colimits, and it is exactly an
[equifibered sequential diagram](synthetic-homotopy-theory.equifibered-sequential-diagrams.md).

The fact that the type of descent data for a sequential diagram is equivalent to
the type of type families over its colimit is recorded in
[`descent-property-sequential-colimits`](synthetic-homotopy-theory.descent-property-sequential-colimits.md).

## Definitions

### Descent data for sequential colimits

```agda
module _
  {l1 : Level} (A : sequential-diagram l1)
  where

  descent-data-sequential-colimit : (l2 : Level) → UU (l1 ⊔ lsuc l2)
  descent-data-sequential-colimit =
    equifibered-sequential-diagram A
```

### Components of descent data for sequential colimits

```agda
module _
  {l1 l2 : Level} {A : sequential-diagram l1}
  (B : descent-data-sequential-colimit A l2)
  where

  family-descent-data-sequential-colimit :
    (n : ℕ) → family-sequential-diagram A n → UU l2
  family-descent-data-sequential-colimit = pr1 B

  equiv-family-descent-data-sequential-colimit :
    (n : ℕ) (a : family-sequential-diagram A n) →
    family-descent-data-sequential-colimit n a ≃
    family-descent-data-sequential-colimit
      ( succ-ℕ n)
      ( map-sequential-diagram A n a)
  equiv-family-descent-data-sequential-colimit = pr2 B

  map-family-descent-data-sequential-colimit :
    (n : ℕ) (a : family-sequential-diagram A n) →
    family-descent-data-sequential-colimit n a →
    family-descent-data-sequential-colimit
      ( succ-ℕ n)
      ( map-sequential-diagram A n a)
  map-family-descent-data-sequential-colimit n a =
    map-equiv (equiv-family-descent-data-sequential-colimit n a)

  is-equiv-map-family-descent-data-sequential-colimit :
    (n : ℕ) (a : family-sequential-diagram A n) →
    is-equiv (map-family-descent-data-sequential-colimit n a)
  is-equiv-map-family-descent-data-sequential-colimit n a =
    is-equiv-map-equiv (equiv-family-descent-data-sequential-colimit n a)

  dependent-sequential-diagram-descent-data : dependent-sequential-diagram A l2
  dependent-sequential-diagram-descent-data =
    dependent-sequential-diagram-equifibered-sequential-diagram B
```

### Morphisms of descent data for sequential colimits

```agda
module _
  {l1 l2 l3 : Level} {A : sequential-diagram l1}
  (B : descent-data-sequential-colimit A l2)
  (C : descent-data-sequential-colimit A l3)
  where

  hom-descent-data-sequential-colimit : UU (l1 ⊔ l2 ⊔ l3)
  hom-descent-data-sequential-colimit =
    hom-dependent-sequential-diagram
      ( dependent-sequential-diagram-equifibered-sequential-diagram B)
      ( dependent-sequential-diagram-equifibered-sequential-diagram C)
```

### Equivalences of descent data for sequential colimits

```agda
module _
  {l1 l2 l3 : Level} {A : sequential-diagram l1}
  (B : descent-data-sequential-colimit A l2)
  (C : descent-data-sequential-colimit A l3)
  where

  equiv-descent-data-sequential-colimit : UU (l1 ⊔ l2 ⊔ l3)
  equiv-descent-data-sequential-colimit =
    equiv-dependent-sequential-diagram
      ( dependent-sequential-diagram-equifibered-sequential-diagram B)
      ( dependent-sequential-diagram-equifibered-sequential-diagram C)

  module _
    (e : equiv-descent-data-sequential-colimit)
    where

    equiv-equiv-descent-data-sequential-colimit :
      (n : ℕ) (a : family-sequential-diagram A n) →
      family-descent-data-sequential-colimit B n a ≃
      family-descent-data-sequential-colimit C n a
    equiv-equiv-descent-data-sequential-colimit =
      equiv-equiv-dependent-sequential-diagram
        ( dependent-sequential-diagram-equifibered-sequential-diagram C)
        ( e)

    map-equiv-descent-data-sequential-colimit :
      (n : ℕ) (a : family-sequential-diagram A n) →
      family-descent-data-sequential-colimit B n a →
      family-descent-data-sequential-colimit C n a
    map-equiv-descent-data-sequential-colimit =
      map-equiv-dependent-sequential-diagram
        ( dependent-sequential-diagram-equifibered-sequential-diagram C)
        ( e)

    is-equiv-map-equiv-descent-data-sequential-colimit :
      (n : ℕ) (a : family-sequential-diagram A n) →
      is-equiv (map-equiv-descent-data-sequential-colimit n a)
    is-equiv-map-equiv-descent-data-sequential-colimit =
      is-equiv-map-equiv-dependent-sequential-diagram
        ( dependent-sequential-diagram-equifibered-sequential-diagram C)
        ( e)

    coh-equiv-descent-data-sequential-colimit :
      coherence-equiv-dependent-sequential-diagram
        ( dependent-sequential-diagram-equifibered-sequential-diagram B)
        ( dependent-sequential-diagram-equifibered-sequential-diagram C)
        ( equiv-equiv-descent-data-sequential-colimit)
    coh-equiv-descent-data-sequential-colimit =
      coh-equiv-dependent-sequential-diagram
        ( dependent-sequential-diagram-equifibered-sequential-diagram C)
        ( e)

    hom-equiv-descent-data-sequential-colimit :
      hom-descent-data-sequential-colimit B C
    hom-equiv-descent-data-sequential-colimit =
      hom-equiv-dependent-sequential-diagram
        ( dependent-sequential-diagram-equifibered-sequential-diagram C)
        ( e)

module _
  {l1 l2 : Level} {A : sequential-diagram l1}
  (B : descent-data-sequential-colimit A l2)
  where

  id-equiv-descent-data-sequential-colimit :
    equiv-descent-data-sequential-colimit B B
  id-equiv-descent-data-sequential-colimit =
    id-equiv-dependent-sequential-diagram
      ( dependent-sequential-diagram-equifibered-sequential-diagram B)

module _
  {l1 l2 l3 l4 : Level} {A : sequential-diagram l1}
  (B : descent-data-sequential-colimit A l2)
  (C : descent-data-sequential-colimit A l3)
  (D : descent-data-sequential-colimit A l4)
  (f : equiv-descent-data-sequential-colimit C D)
  (e : equiv-descent-data-sequential-colimit B C)
  where

  comp-equiv-descent-data-sequential-colimit :
    equiv-descent-data-sequential-colimit B D
  comp-equiv-descent-data-sequential-colimit =
    comp-equiv-dependent-sequential-diagram
      ( dependent-sequential-diagram-equifibered-sequential-diagram B)
      ( dependent-sequential-diagram-equifibered-sequential-diagram C)
      ( dependent-sequential-diagram-equifibered-sequential-diagram D)
      ( f)
      ( e)

module _
  {l1 l2 l3 : Level} {A : sequential-diagram l1}
  (B : descent-data-sequential-colimit A l2)
  (C : descent-data-sequential-colimit A l3)
  where

  inv-equiv-descent-data-sequential-colimit :
    equiv-descent-data-sequential-colimit B C →
    equiv-descent-data-sequential-colimit C B
  inv-equiv-descent-data-sequential-colimit e =
    inv-equiv-dependent-sequential-diagram
      ( dependent-sequential-diagram-equifibered-sequential-diagram C)
      ( e)
```

### Descent data induced by families over cocones under sequential diagrams

```agda
module _
  {l1 l2 : Level} {A : sequential-diagram l1}
  {X : UU l2} (c : cocone-sequential-diagram A X)
  where

  descent-data-family-cocone-sequential-diagram :
    {l3 : Level} → (X → UU l3) → descent-data-sequential-colimit A l3
  descent-data-family-cocone-sequential-diagram =
    equifibered-sequential-diagram-family-cocone c
```
