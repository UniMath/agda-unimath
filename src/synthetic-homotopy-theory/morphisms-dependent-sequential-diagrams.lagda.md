# Morphisms of dependent sequential diagrams

```agda
module synthetic-homotopy-theory.morphisms-dependent-sequential-diagrams where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.commuting-squares-of-maps
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import synthetic-homotopy-theory.dependent-sequential-diagrams
open import synthetic-homotopy-theory.morphisms-sequential-diagrams
open import synthetic-homotopy-theory.sequential-diagrams
```

</details>

## Idea

Consider two
[dependent sequential diagrams](synthetic-homotopy-theory.dependent-sequential-diagrams.md)

```text
     b₀      b₁      b₂            c₀      c₁      c₂
 B₀ ---> B₁ ---> B₂ ---> ⋯     C₀ ---> C₁ ---> C₂ ---> ⋯
 |       |       |             |       |       |
 |       |       |             |       |       |
 ↡       ↡       ↡             ↡       ↡       ↡
 A₀ ---> A₁ ---> A₂ ---> ⋯     A₀ ---> A₁ ---> A₂ ---> ⋯ .
     a₀      a₁      a₂            a₀      a₁      a₂
```

A
{{#concept "morphism of dependent sequential diagrams" Agda=hom-dependent-sequential-diagram}}
between them is a family of fiberwise maps

```text
hₙ : (a : Aₙ) → Bₙ a → Cₙ a
```

[equipped](foundation.structure.md) with a family of fiberwise
[homotopies](foundation-core.homotopies.md) making the squares

```text
                 hₙ a
     Bₙ a -----------------> Cₙ a
       |                       |
  bₙ a |                       | cₙ a
       |                       |
       ∨                       ∨
  Bₙ₊₁ (aₙ a) ----------> Cₙ₊₁ (aₙ a)
              hₙ₊₁ (aₙ a)
```

[commute](foundation-core.commuting-squares-of-maps.md).

## Definitions

### Morphisms of dependent sequential diagrams

```agda
module _
  {l1 l2 l3 : Level} {A : sequential-diagram l1}
  (B : dependent-sequential-diagram A l2)
  (C : dependent-sequential-diagram A l3)
  where

  coherence-hom-dependent-sequential-diagram :
    ( (n : ℕ) (a : family-sequential-diagram A n) →
      family-dependent-sequential-diagram B n a →
      family-dependent-sequential-diagram C n a) →
    UU (l1 ⊔ l2 ⊔ l3)
  coherence-hom-dependent-sequential-diagram h =
    (n : ℕ) (a : family-sequential-diagram A n) →
    coherence-square-maps
      ( h n a)
      ( map-dependent-sequential-diagram B n a)
      ( map-dependent-sequential-diagram C n a)
      ( h (succ-ℕ n) (map-sequential-diagram A n a))

  hom-dependent-sequential-diagram : UU (l1 ⊔ l2 ⊔ l3)
  hom-dependent-sequential-diagram =
    Σ ( (n : ℕ) (a : family-sequential-diagram A n) →
        family-dependent-sequential-diagram B n a →
        family-dependent-sequential-diagram C n a)
      ( coherence-hom-dependent-sequential-diagram)
```

### Components of a morphism of sequential diagrams

```agda
module _
  {l1 l2 l3 : Level} {A : sequential-diagram l1}
  {B : dependent-sequential-diagram A l2}
  (C : dependent-sequential-diagram A l3)
  (h : hom-dependent-sequential-diagram B C)
  where

  map-hom-dependent-sequential-diagram :
    (n : ℕ) (a : family-sequential-diagram A n) →
    family-dependent-sequential-diagram B n a →
    family-dependent-sequential-diagram C n a
  map-hom-dependent-sequential-diagram = pr1 h

  coh-hom-dependent-sequential-diagram :
    coherence-hom-dependent-sequential-diagram B C
      ( map-hom-dependent-sequential-diagram)
  coh-hom-dependent-sequential-diagram = pr2 h
```

### Morphisms of dependent sequential diagrams over morphisms of sequential diagrams

```agda
module _
  {l1 l2 l3 l4 : Level} {A : sequential-diagram l1} {B : sequential-diagram l2}
  (P : dependent-sequential-diagram A l3)
  (Q : dependent-sequential-diagram B l4)
  (h : hom-sequential-diagram A B)
  where

  hom-dependent-sequential-diagram-over : UU (l1 ⊔ l3 ⊔ l4)
  hom-dependent-sequential-diagram-over =
    Σ ( (n : ℕ) (a : family-sequential-diagram A n) →
        family-dependent-sequential-diagram P n a →
        family-dependent-sequential-diagram Q n
          ( map-hom-sequential-diagram B h n a))
      ( λ f →
        (n : ℕ) (a : family-sequential-diagram A n) →
        (p : family-dependent-sequential-diagram P n a) →
        dependent-identification
          ( family-dependent-sequential-diagram Q (succ-ℕ n))
          ( naturality-map-hom-sequential-diagram B h n a)
          ( map-dependent-sequential-diagram Q n
            ( map-hom-sequential-diagram B h n a)
            ( f n a p))
          ( f (succ-ℕ n) (map-sequential-diagram A n a) (map-dependent-sequential-diagram P n a p)))
```

## Properties

### TODO

```agda
module _
  {l1 l2 l3 : Level} {A : sequential-diagram l1} {B : sequential-diagram l2}
  (h : hom-sequential-diagram A B)
  where

  pullback-hom-dependent-sequential-diagram :
    dependent-sequential-diagram B l3 →
    dependent-sequential-diagram A l3
  pr1 (pullback-hom-dependent-sequential-diagram Q) n a =
    family-dependent-sequential-diagram Q n
      ( map-hom-sequential-diagram B h n a)
  pr2 (pullback-hom-dependent-sequential-diagram Q) n a q =
    tr
      ( family-dependent-sequential-diagram Q (succ-ℕ n))
      ( naturality-map-hom-sequential-diagram B h n a)
      ( map-dependent-sequential-diagram Q n
        ( map-hom-sequential-diagram B h n a)
        ( q))
```

```agda
module _
  {l1 l2 l3 l4 : Level} {A : sequential-diagram l1} {B : sequential-diagram l2}
  {P : dependent-sequential-diagram A l3}
  {Q : dependent-sequential-diagram B l4}
  (h : hom-sequential-diagram A B)
  where

  open import foundation.homotopies

  hom-dep-seq-diag-over-hom-dep-seq-diag :
    hom-dependent-sequential-diagram P
      ( pullback-hom-dependent-sequential-diagram h Q) →
    hom-dependent-sequential-diagram-over P Q h
  pr1 (hom-dep-seq-diag-over-hom-dep-seq-diag h') =
    map-hom-dependent-sequential-diagram (pullback-hom-dependent-sequential-diagram h Q) h'
  pr2 (hom-dep-seq-diag-over-hom-dep-seq-diag h') n a =
    inv-htpy (coh-hom-dependent-sequential-diagram (pullback-hom-dependent-sequential-diagram h Q) h' n a)
```
