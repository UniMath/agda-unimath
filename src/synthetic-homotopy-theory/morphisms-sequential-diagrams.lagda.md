# Morphisms of sequential diagrams

```agda
module synthetic-homotopy-theory.morphisms-sequential-diagrams where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.binary-homotopies
open import foundation.commuting-squares-of-homotopies
open import foundation.commuting-squares-of-maps
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import synthetic-homotopy-theory.dependent-sequential-diagrams
open import synthetic-homotopy-theory.sequential-diagrams
```

</details>

## Idea

A **morphism between
[sequential diagrams](synthetic-homotopy-theory.sequential-diagrams.md)**
`f : (A, a) → (B, b)` is a [sequence](foundation.dependent-sequences.md) of maps
`fₙ : Aₙ → Bₙ` satisfying the naturality condition that all squares of the form

```text
        aₙ
    Aₙ ---> Aₙ₊₁
    |       |
 fₙ |       | fₙ₊₁
    ∨       ∨
    Bₙ ---> Bₙ₊₁
        bₙ
```

[commute](foundation.commuting-squares-of-maps.md).

## Definitions

### Morphisms of sequential diagrams

```agda
module _
  { l1 l2 : Level} (A : sequential-diagram l1) (B : sequential-diagram l2)
  where

  naturality-hom-sequential-diagram :
    ( h :
      ( n : ℕ) →
      family-sequential-diagram A n → family-sequential-diagram B n) →
    UU (l1 ⊔ l2)
  naturality-hom-sequential-diagram h =
    ( n : ℕ) →
    ( map-sequential-diagram B n ∘ h n) ~
    ( h (succ-ℕ n) ∘ map-sequential-diagram A n)

  hom-sequential-diagram : UU (l1 ⊔ l2)
  hom-sequential-diagram =
    Σ ( (n : ℕ) → family-sequential-diagram A n → family-sequential-diagram B n)
      ( naturality-hom-sequential-diagram)
```

### Components of morphisms of sequential diagrams

_Implementation note:_ Ideally we would have both the domain and codomain of a
morphism of sequential diagrams inferred by Agda. Unfortunately that's not the
case with the current implementation, and the codomain needs to be provided
explicitly. This arises also in
[equivalences of sequential diagrams](synthetic-homotopy-theory.equivalences-sequential-diagrams.md).

```agda
module _
  { l1 l2 : Level} {A : sequential-diagram l1} (B : sequential-diagram l2)
  ( h : hom-sequential-diagram A B)
  where

  map-hom-sequential-diagram :
    ( n : ℕ) → family-sequential-diagram A n → family-sequential-diagram B n
  map-hom-sequential-diagram = pr1 h

  naturality-map-hom-sequential-diagram :
    naturality-hom-sequential-diagram A B map-hom-sequential-diagram
  naturality-map-hom-sequential-diagram = pr2 h
```

### The identity morphism of sequential diagrams

All sequential diagrams have an **identity morphism** constructed from the
identity function on the underlying types.

```agda
module _
  { l1 : Level} (A : sequential-diagram l1)
  where

  id-hom-sequential-diagram : hom-sequential-diagram A A
  pr1 id-hom-sequential-diagram n = id
  pr2 id-hom-sequential-diagram n = refl-htpy
```

### Composition of morphisms of sequential diagrams

**Composition of morphisms** is induced by composition of the underlying maps
and by pasting diagrams.

```agda
module _
  { l1 l2 l3 : Level} (A : sequential-diagram l1) (B : sequential-diagram l2)
  ( C : sequential-diagram l3)
  ( g : hom-sequential-diagram B C) (f : hom-sequential-diagram A B)
  where

  map-comp-hom-sequential-diagram :
    (n : ℕ) → family-sequential-diagram A n → family-sequential-diagram C n
  map-comp-hom-sequential-diagram n =
    map-hom-sequential-diagram C g n ∘ map-hom-sequential-diagram B f n

  naturality-comp-hom-sequential-diagram :
    naturality-hom-sequential-diagram A C map-comp-hom-sequential-diagram
  naturality-comp-hom-sequential-diagram n =
    pasting-vertical-coherence-square-maps
      ( map-sequential-diagram A n)
      ( map-hom-sequential-diagram B f n)
      ( map-hom-sequential-diagram B f (succ-ℕ n))
      ( map-sequential-diagram B n)
      ( map-hom-sequential-diagram C g n)
      ( map-hom-sequential-diagram C g (succ-ℕ n))
      ( map-sequential-diagram C n)
      ( naturality-map-hom-sequential-diagram B f n)
      ( naturality-map-hom-sequential-diagram C g n)

  comp-hom-sequential-diagram :
    hom-sequential-diagram A C
  pr1 comp-hom-sequential-diagram = map-comp-hom-sequential-diagram
  pr2 comp-hom-sequential-diagram = naturality-comp-hom-sequential-diagram
```

### Homotopies between morphisms of sequential diagrams

A **homotopy** between morphisms `f, g : (A, a) → (B, b)` consists of a
[sequence](foundation.dependent-sequences.md) of
[homotopies](foundation.homotopies.md) `Hₙ : fₙ ~ gₙ` and a coherence datum
filling the cylinders

```text
              aₙ
      Aₙ ----------> Aₙ₊₁
      / \            / \
     / Hₙ\          /Hₙ₊₁\
 fₙ |  => | gₙ fₙ₊₁ |  => | gₙ₊₁
     \   /          \   /
      \ /            \ /
      Bₙ ----------> Bₙ₊₁.
              bₙ
```

```agda
module _
  { l1 l2 : Level} {A : sequential-diagram l1} (B : sequential-diagram l2)
  ( f g : hom-sequential-diagram A B)
  where

  coherence-htpy-hom-sequential-diagram :
    ( H :
      ( n : ℕ) →
      ( map-hom-sequential-diagram B f n) ~
      ( map-hom-sequential-diagram B g n)) →
    UU (l1 ⊔ l2)
  coherence-htpy-hom-sequential-diagram H =
    ( n : ℕ) →
    coherence-square-homotopies
      ( map-sequential-diagram B n ·l H n)
      ( naturality-map-hom-sequential-diagram B f n)
      ( naturality-map-hom-sequential-diagram B g n)
      ( H (succ-ℕ n) ·r map-sequential-diagram A n)

  htpy-hom-sequential-diagram : UU (l1 ⊔ l2)
  htpy-hom-sequential-diagram =
    Σ ( ( n : ℕ) →
        ( map-hom-sequential-diagram B f n) ~
        ( map-hom-sequential-diagram B g n))
      ( coherence-htpy-hom-sequential-diagram)
```

### Components of homotopies between morphisms of sequential diagrams

```agda
module _
  { l1 l2 : Level} {A : sequential-diagram l1} (B : sequential-diagram l2)
  { f g : hom-sequential-diagram A B}
  ( H : htpy-hom-sequential-diagram B f g)
  where

  htpy-htpy-hom-sequential-diagram :
    ( n : ℕ) →
    ( map-hom-sequential-diagram B f n) ~
    ( map-hom-sequential-diagram B g n)
  htpy-htpy-hom-sequential-diagram = pr1 H

  coherence-htpy-htpy-hom-sequential-diagram :
    coherence-htpy-hom-sequential-diagram B f g htpy-htpy-hom-sequential-diagram
  coherence-htpy-htpy-hom-sequential-diagram = pr2 H
```

## Properties

### Characterization of equality of morphisms of sequential diagrams

[Equality](foundation.identity-types.md) of morphisms of sequential diagrams is
captured by a homotopy between them.

```agda
module _
  { l1 l2 : Level} (A : sequential-diagram l1) (B : sequential-diagram l2)
  where

  refl-htpy-hom-sequential-diagram :
    ( f : hom-sequential-diagram A B) → htpy-hom-sequential-diagram B f f
  pr1 (refl-htpy-hom-sequential-diagram f) = ev-pair refl-htpy
  pr2 (refl-htpy-hom-sequential-diagram f) = ev-pair right-unit-htpy

  htpy-eq-sequential-diagram :
    ( f f' : hom-sequential-diagram A B) →
    ( f ＝ f') → htpy-hom-sequential-diagram B f f'
  htpy-eq-sequential-diagram f .f refl = refl-htpy-hom-sequential-diagram f

  abstract
    is-torsorial-htpy-sequential-diagram :
      ( f : hom-sequential-diagram A B) →
      is-torsorial (htpy-hom-sequential-diagram B f)
    is-torsorial-htpy-sequential-diagram f =
      is-torsorial-Eq-structure
        ( is-torsorial-binary-htpy (map-hom-sequential-diagram B f))
        ( map-hom-sequential-diagram B f , ev-pair refl-htpy)
        ( is-torsorial-Eq-Π
          ( λ n →
            is-torsorial-htpy
              ( naturality-map-hom-sequential-diagram B f n ∙h refl-htpy)))

    is-equiv-htpy-eq-sequential-diagram :
      ( f f' : hom-sequential-diagram A B) →
      is-equiv (htpy-eq-sequential-diagram f f')
    is-equiv-htpy-eq-sequential-diagram f =
      fundamental-theorem-id
        ( is-torsorial-htpy-sequential-diagram f)
        ( htpy-eq-sequential-diagram f)

  extensionality-hom-sequential-diagram :
    ( f f' : hom-sequential-diagram A B) →
    ( f ＝ f') ≃ htpy-hom-sequential-diagram B f f'
  pr1 (extensionality-hom-sequential-diagram f f') =
    htpy-eq-sequential-diagram f f'
  pr2 (extensionality-hom-sequential-diagram f f') =
    is-equiv-htpy-eq-sequential-diagram f f'

  eq-htpy-sequential-diagram :
    ( f f' : hom-sequential-diagram A B) →
    htpy-hom-sequential-diagram B f f' → (f ＝ f')
  eq-htpy-sequential-diagram f f' =
    map-inv-equiv (extensionality-hom-sequential-diagram f f')
```

### Composition of morphisms of sequential diagrams is associative

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : sequential-diagram l1} {B : sequential-diagram l2}
  {C : sequential-diagram l3} {D : sequential-diagram l4}
  (f : hom-sequential-diagram A B) (g : hom-sequential-diagram B C)
  (h : hom-sequential-diagram C D)
  where

  assoc-comp-hom-sequential-diagram :
    htpy-hom-sequential-diagram D
      ( comp-hom-sequential-diagram A B D
        ( comp-hom-sequential-diagram B C D h g)
        ( f))
      ( comp-hom-sequential-diagram A C D h
        ( comp-hom-sequential-diagram A B C g f))
  pr1 assoc-comp-hom-sequential-diagram n = refl-htpy
  pr2 assoc-comp-hom-sequential-diagram n =
    right-unit-htpy ∙h
    assoc-htpy
      ( naturality-map-hom-sequential-diagram D h n ·r
        ( map-hom-sequential-diagram C g n ∘
          map-hom-sequential-diagram B f n))
      ( map-hom-sequential-diagram D h (succ-ℕ n) ·l
        naturality-map-hom-sequential-diagram C g n ·r
        map-hom-sequential-diagram B f n)
      ( ( map-hom-sequential-diagram D h (succ-ℕ n) ∘
          map-hom-sequential-diagram C g (succ-ℕ n)) ·l
        naturality-map-hom-sequential-diagram B f n) ∙h
    left-whisker-concat-htpy
      ( naturality-map-hom-sequential-diagram D h n ·r
        ( map-hom-sequential-diagram C g n ∘ map-hom-sequential-diagram B f n))
      ( left-whisker-concat-htpy
          ( map-hom-sequential-diagram D h (succ-ℕ n) ·l
            naturality-map-hom-sequential-diagram C g n ·r
            map-hom-sequential-diagram B f n)
          ( inv-preserves-comp-left-whisker-comp
            ( map-hom-sequential-diagram D h (succ-ℕ n))
            ( map-hom-sequential-diagram C g (succ-ℕ n))
            ( naturality-map-hom-sequential-diagram B f n)) ∙h
        inv-htpy
          ( distributive-left-whisker-comp-concat
            ( map-hom-sequential-diagram D h (succ-ℕ n))
            ( naturality-map-hom-sequential-diagram C g n ·r
              map-hom-sequential-diagram B f n)
            ( map-hom-sequential-diagram C g (succ-ℕ n) ·l
              naturality-map-hom-sequential-diagram B f n)))
```
