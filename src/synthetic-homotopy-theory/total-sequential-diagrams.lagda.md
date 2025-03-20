# Total sequential diagrams of dependent sequential diagrams

```agda
open import foundation.function-extensionality-axiom

module
  synthetic-homotopy-theory.total-sequential-diagrams
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.functoriality-dependent-pair-types funext
open import foundation.homotopies funext
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-sequential-diagrams funext
open import synthetic-homotopy-theory.dependent-sequential-diagrams funext
open import synthetic-homotopy-theory.equivalences-dependent-sequential-diagrams funext
open import synthetic-homotopy-theory.equivalences-sequential-diagrams funext
open import synthetic-homotopy-theory.functoriality-sequential-colimits funext
open import synthetic-homotopy-theory.morphisms-sequential-diagrams funext
open import synthetic-homotopy-theory.sequential-colimits funext
open import synthetic-homotopy-theory.sequential-diagrams funext
open import synthetic-homotopy-theory.universal-property-sequential-colimits funext
```

</details>

## Idea

The
{{#concept "total diagram" Disambiguation="dependent sequential diagrams" Agda=total-sequential-diagram}}
of a
[dependent sequential diagram](synthetic-homotopy-theory.dependent-sequential-diagrams.md)
`B : (A, a) → 𝒰` is the
[sequential diagram](synthetic-homotopy-theory.sequential-diagrams.md)
consisting of [total spaces](foundation.dependent-pair-types.md) `Σ Aₙ Bₙ` and
total maps.

## Definitions

### The total sequential diagram of a dependent sequential diagram

```agda
module _
  {l1 l2 : Level}
  {A : sequential-diagram l1} (B : dependent-sequential-diagram A l2)
  where

  family-total-sequential-diagram : ℕ → UU (l1 ⊔ l2)
  family-total-sequential-diagram n =
    Σ (family-sequential-diagram A n)
      (family-dependent-sequential-diagram B n)

  map-total-sequential-diagram :
    (n : ℕ) → family-total-sequential-diagram n →
    family-total-sequential-diagram (succ-ℕ n)
  map-total-sequential-diagram n =
    map-Σ
      ( family-dependent-sequential-diagram B (succ-ℕ n))
      ( map-sequential-diagram A n)
      ( map-dependent-sequential-diagram B n)

  total-sequential-diagram : sequential-diagram (l1 ⊔ l2)
  pr1 total-sequential-diagram = family-total-sequential-diagram
  pr2 total-sequential-diagram = map-total-sequential-diagram
```

### The projection morphism onto the base of the total sequential diagram

```agda
module _
  {l1 l2 : Level}
  {A : sequential-diagram l1} (B : dependent-sequential-diagram A l2)
  where

  pr1-total-sequential-diagram :
    hom-sequential-diagram
      ( total-sequential-diagram B)
      ( A)
  pr1 pr1-total-sequential-diagram n = pr1
  pr2 pr1-total-sequential-diagram n = refl-htpy
```

### The induced projection map on sequential colimits

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : sequential-diagram l1} (B : dependent-sequential-diagram A l2)
  {X : UU l3} {c : cocone-sequential-diagram (total-sequential-diagram B) X}
  (up-c : universal-property-sequential-colimit c)
  {Y : UU l4} (c' : cocone-sequential-diagram A Y)
  where

  pr1-sequential-colimit-total-sequential-diagram : X → Y
  pr1-sequential-colimit-total-sequential-diagram =
    map-sequential-colimit-hom-sequential-diagram
      ( up-c)
      ( c')
      ( pr1-total-sequential-diagram B)
```

### The induced projection map on standard sequential colimits

```agda
module _
  {l1 l2 : Level}
  {A : sequential-diagram l1} (B : dependent-sequential-diagram A l2)
  where

  pr1-standard-sequential-colimit-total-sequential-diagram :
    standard-sequential-colimit (total-sequential-diagram B) →
    standard-sequential-colimit A
  pr1-standard-sequential-colimit-total-sequential-diagram =
    map-hom-standard-sequential-colimit A
      ( pr1-total-sequential-diagram B)
```

## Properties

### Equivalences of dependent sequential diagrams induce equivalences on the total sequential diagrams

```agda
module _
  {l1 l2 l3 : Level} {A : sequential-diagram l1}
  (B : dependent-sequential-diagram A l2)
  (C : dependent-sequential-diagram A l3)
  (e : equiv-dependent-sequential-diagram B C)
  where

  equiv-total-sequential-diagram-equiv-dependent-sequential-diagram :
    equiv-sequential-diagram
      ( total-sequential-diagram B)
      ( total-sequential-diagram C)
  pr1 equiv-total-sequential-diagram-equiv-dependent-sequential-diagram n =
    equiv-tot (equiv-equiv-dependent-sequential-diagram C e n)
  pr2 equiv-total-sequential-diagram-equiv-dependent-sequential-diagram n =
    coherence-square-maps-Σ
      ( family-dependent-sequential-diagram C (succ-ℕ n))
      ( map-dependent-sequential-diagram B n)
      ( map-equiv-dependent-sequential-diagram C e n)
      ( map-equiv-dependent-sequential-diagram C e (succ-ℕ n))
      ( map-dependent-sequential-diagram C n)
      { refl-htpy}
      ( λ a → inv-htpy (coh-equiv-dependent-sequential-diagram C e n a))
```
