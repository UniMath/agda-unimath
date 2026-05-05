# Families with descent data for sequential colimits

```agda
module synthetic-homotopy-theory.families-descent-data-sequential-colimits where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.commuting-squares-of-maps
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-sequential-diagrams
open import synthetic-homotopy-theory.dependent-sequential-diagrams
open import synthetic-homotopy-theory.descent-data-sequential-colimits
open import synthetic-homotopy-theory.sequential-diagrams
```

</details>

## Idea

As shown in
[`descent-property-sequential-colimits`](synthetic-homotopy-theory.descent-sequential-colimits.md),
the type of type families over
[sequential colimits](synthetic-homotopy-theory.universal-property-sequential-colimits.md)
is [equivalent](foundation-core.equivalences.md) to
[descent data](synthetic-homotopy-theory.descent-data-sequential-colimits.md).

Sometimes it is useful to consider tripes `(P, B, e)` where `P : X → 𝒰` is a
type family, `B` is descent data, and `e` is an equivalence between `B` and the
descent data induced by `P`. The type of such pairs `(B, e)` is
[contractible](foundation-core.contractible-types.md), so the type of these
triples is equivalent to the type of type families over `X`, but it may be more
ergonomic to characterize descent data of a particular type family, and then
have theorems know about this characterization, rather than transporting along
such a characterization after the fact.

## Definitions

### Families over a cocone equipped with corresponding descent data for sequential colimits

```agda
module _
  {l1 l2 : Level} {A : sequential-diagram l1}
  {X : UU l2} (c : cocone-sequential-diagram A X)
  where

  family-with-descent-data-sequential-colimit :
    (l3 : Level) → UU (l1 ⊔ l2 ⊔ lsuc l3)
  family-with-descent-data-sequential-colimit l3 =
    Σ ( X → UU l3)
      ( λ P →
        Σ ( descent-data-sequential-colimit A l3)
          ( λ B →
            equiv-descent-data-sequential-colimit
              ( B)
              ( descent-data-family-cocone-sequential-diagram c P)))
```

### Components of a family with corresponding descent data for sequential colimits

```agda
module _
  {l1 l2 l3 : Level} {A : sequential-diagram l1}
  {X : UU l2} {c : cocone-sequential-diagram A X}
  (P : family-with-descent-data-sequential-colimit c l3)
  where

  family-cocone-family-with-descent-data-sequential-colimit : X → UU l3
  family-cocone-family-with-descent-data-sequential-colimit = pr1 P

  descent-data-family-with-descent-data-sequential-colimit :
    descent-data-sequential-colimit A l3
  descent-data-family-with-descent-data-sequential-colimit = pr1 (pr2 P)

  family-family-with-descent-data-sequential-colimit :
    (n : ℕ) → family-sequential-diagram A n → UU l3
  family-family-with-descent-data-sequential-colimit =
    family-descent-data-sequential-colimit
      ( descent-data-family-with-descent-data-sequential-colimit)

  equiv-family-family-with-descent-data-sequential-colimit :
    (n : ℕ) (a : family-sequential-diagram A n) →
    family-family-with-descent-data-sequential-colimit n a ≃
    family-family-with-descent-data-sequential-colimit
      ( succ-ℕ n)
      ( map-sequential-diagram A n a)
  equiv-family-family-with-descent-data-sequential-colimit =
    equiv-family-descent-data-sequential-colimit
      ( descent-data-family-with-descent-data-sequential-colimit)

  map-family-family-with-descent-data-sequential-colimit :
    (n : ℕ) (a : family-sequential-diagram A n) →
    family-family-with-descent-data-sequential-colimit n a →
    family-family-with-descent-data-sequential-colimit
      ( succ-ℕ n)
      ( map-sequential-diagram A n a)
  map-family-family-with-descent-data-sequential-colimit =
    map-family-descent-data-sequential-colimit
      ( descent-data-family-with-descent-data-sequential-colimit)

  is-equiv-map-family-family-with-descent-data-sequential-colimit :
    (n : ℕ) (a : family-sequential-diagram A n) →
    is-equiv (map-family-family-with-descent-data-sequential-colimit n a)
  is-equiv-map-family-family-with-descent-data-sequential-colimit =
    is-equiv-map-family-descent-data-sequential-colimit
      ( descent-data-family-with-descent-data-sequential-colimit)

  dependent-sequential-diagram-family-with-descent-data-sequential-colimit :
    dependent-sequential-diagram A l3
  dependent-sequential-diagram-family-with-descent-data-sequential-colimit =
    dependent-sequential-diagram-descent-data
      ( descent-data-family-with-descent-data-sequential-colimit)

  equiv-descent-data-family-with-descent-data-sequential-colimit :
    equiv-descent-data-sequential-colimit
      ( descent-data-family-with-descent-data-sequential-colimit)
      ( descent-data-family-cocone-sequential-diagram c
        ( family-cocone-family-with-descent-data-sequential-colimit))
  equiv-descent-data-family-with-descent-data-sequential-colimit = pr2 (pr2 P)

  equiv-equiv-descent-data-family-with-descent-data-sequential-colimit :
    (n : ℕ) (a : family-sequential-diagram A n) →
    family-descent-data-sequential-colimit
      ( descent-data-family-with-descent-data-sequential-colimit)
      ( n)
      ( a) ≃
    family-cocone-family-with-descent-data-sequential-colimit
      ( map-cocone-sequential-diagram c n a)
  equiv-equiv-descent-data-family-with-descent-data-sequential-colimit =
    equiv-equiv-descent-data-sequential-colimit
      ( descent-data-family-with-descent-data-sequential-colimit)
      ( descent-data-family-cocone-sequential-diagram c
        ( family-cocone-family-with-descent-data-sequential-colimit))
      ( equiv-descent-data-family-with-descent-data-sequential-colimit)

  map-equiv-descent-data-family-with-descent-data-sequential-colimit :
    (n : ℕ) (a : family-sequential-diagram A n) →
    family-descent-data-sequential-colimit
      ( descent-data-family-with-descent-data-sequential-colimit)
      ( n)
      ( a) →
    family-cocone-family-with-descent-data-sequential-colimit
      ( map-cocone-sequential-diagram c n a)
  map-equiv-descent-data-family-with-descent-data-sequential-colimit =
    map-equiv-descent-data-sequential-colimit
      ( descent-data-family-with-descent-data-sequential-colimit)
      ( descent-data-family-cocone-sequential-diagram c
        ( family-cocone-family-with-descent-data-sequential-colimit))
      ( equiv-descent-data-family-with-descent-data-sequential-colimit)

  is-equiv-map-equiv-descent-data-family-with-descent-data-sequential-colimit :
    (n : ℕ) (a : family-sequential-diagram A n) →
    is-equiv
      ( map-equiv-descent-data-family-with-descent-data-sequential-colimit n a)
  is-equiv-map-equiv-descent-data-family-with-descent-data-sequential-colimit =
    is-equiv-map-equiv-descent-data-sequential-colimit
      ( descent-data-family-with-descent-data-sequential-colimit)
      ( descent-data-family-cocone-sequential-diagram c
        ( family-cocone-family-with-descent-data-sequential-colimit))
      ( equiv-descent-data-family-with-descent-data-sequential-colimit)

  coherence-square-equiv-descent-data-family-with-descent-data-sequential-colimit :
    (n : ℕ) (a : family-sequential-diagram A n) →
    coherence-square-maps
      ( map-equiv-descent-data-family-with-descent-data-sequential-colimit n a)
      ( map-family-family-with-descent-data-sequential-colimit n a)
      ( tr
        ( family-cocone-family-with-descent-data-sequential-colimit)
        ( coherence-cocone-sequential-diagram c n a))
      ( map-equiv-descent-data-family-with-descent-data-sequential-colimit
        ( succ-ℕ n)
        ( map-sequential-diagram A n a))
  coherence-square-equiv-descent-data-family-with-descent-data-sequential-colimit =
    coh-equiv-descent-data-sequential-colimit
      ( descent-data-family-with-descent-data-sequential-colimit)
      ( descent-data-family-cocone-sequential-diagram c
        ( family-cocone-family-with-descent-data-sequential-colimit))
      ( equiv-descent-data-family-with-descent-data-sequential-colimit)
```

### A type family equipped with its induced descent data for sequential colimits

```agda
module _
  {l1 l2 l3 : Level} {A : sequential-diagram l1}
  {X : UU l2} (c : cocone-sequential-diagram A X)
  (P : X → UU l3)
  where

  family-with-descent-data-family-cocone-sequential-diagram :
    family-with-descent-data-sequential-colimit c l3
  pr1 family-with-descent-data-family-cocone-sequential-diagram = P
  pr1 (pr2 family-with-descent-data-family-cocone-sequential-diagram) =
    descent-data-family-cocone-sequential-diagram c P
  pr2 (pr2 family-with-descent-data-family-cocone-sequential-diagram) =
    id-equiv-descent-data-sequential-colimit
      ( descent-data-family-cocone-sequential-diagram c P)
```
