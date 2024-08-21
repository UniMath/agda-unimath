# Equivalances of dependent sequential diagrams

```agda
module synthetic-homotopy-theory.equivalences-dependent-sequential-diagrams where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.commuting-squares-of-maps
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.univalence
open import foundation.universe-levels

open import synthetic-homotopy-theory.dependent-sequential-diagrams
open import synthetic-homotopy-theory.morphisms-dependent-sequential-diagrams
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

An
{{#concept "equivalence of dependent sequential diagrams" Agda=equiv-dependent-sequential-diagram}}
between them is a family of
[fiberwise equivalences](foundation-core.families-of-equivalences.md)

```text
eₙ : (a : Aₙ) → Bₙ a ≃ Cₙ a
```

[equipped](foundation.structure.md) with a family of fiberwise
[homotopies](foundation-core.homotopies.md) making the squares

```text
                 eₙ a
     Bₙ a -----------------> Cₙ a
       |          ≃            |
  bₙ a |                       | cₙ a
       |                       |
       ∨          ≃            ∨
  Bₙ₊₁ (aₙ a) ----------> Cₙ₊₁ (aₙ a)
              eₙ₊₁ (aₙ a)
```

[commute](foundation-core.commuting-squares-of-maps.md).

## Definitions

### Equivalences of dependent sequential diagrams

```agda
module _
  {l1 l2 l3 : Level} {A : sequential-diagram l1}
  (B : dependent-sequential-diagram A l2)
  (C : dependent-sequential-diagram A l3)
  where

  coherence-equiv-dependent-sequential-diagram :
    ( (n : ℕ) (a : family-sequential-diagram A n) →
      family-dependent-sequential-diagram B n a ≃
      family-dependent-sequential-diagram C n a) →
    UU (l1 ⊔ l2 ⊔ l3)
  coherence-equiv-dependent-sequential-diagram h =
    (n : ℕ) (a : family-sequential-diagram A n) →
    coherence-square-maps
      ( map-equiv (h n a))
      ( map-dependent-sequential-diagram B n a)
      ( map-dependent-sequential-diagram C n a)
      ( map-equiv (h (succ-ℕ n) (map-sequential-diagram A n a)))

  equiv-dependent-sequential-diagram : UU (l1 ⊔ l2 ⊔ l3)
  equiv-dependent-sequential-diagram =
    Σ ( (n : ℕ) (a : family-sequential-diagram A n) →
        family-dependent-sequential-diagram B n a ≃
        family-dependent-sequential-diagram C n a)
      ( coherence-equiv-dependent-sequential-diagram)
```

### Components of an equivalence of dependent sequential diagrams

```agda
module _
  {l1 l2 l3 : Level} {A : sequential-diagram l1}
  {B : dependent-sequential-diagram A l2}
  (C : dependent-sequential-diagram A l3)
  (e : equiv-dependent-sequential-diagram B C)
  where

  equiv-equiv-dependent-sequential-diagram :
    (n : ℕ) (a : family-sequential-diagram A n) →
    family-dependent-sequential-diagram B n a ≃
    family-dependent-sequential-diagram C n a
  equiv-equiv-dependent-sequential-diagram = pr1 e

  map-equiv-dependent-sequential-diagram :
    (n : ℕ) (a : family-sequential-diagram A n) →
    family-dependent-sequential-diagram B n a →
    family-dependent-sequential-diagram C n a
  map-equiv-dependent-sequential-diagram n a =
    map-equiv (equiv-equiv-dependent-sequential-diagram n a)

  is-equiv-map-equiv-dependent-sequential-diagram :
    (n : ℕ) (a : family-sequential-diagram A n) →
    is-equiv (map-equiv-dependent-sequential-diagram n a)
  is-equiv-map-equiv-dependent-sequential-diagram n a =
    is-equiv-map-equiv (equiv-equiv-dependent-sequential-diagram n a)

  coh-equiv-dependent-sequential-diagram :
    coherence-equiv-dependent-sequential-diagram B C
      ( equiv-equiv-dependent-sequential-diagram)
  coh-equiv-dependent-sequential-diagram = pr2 e

  hom-equiv-dependent-sequential-diagram :
    hom-dependent-sequential-diagram B C
  pr1 hom-equiv-dependent-sequential-diagram =
    map-equiv-dependent-sequential-diagram
  pr2 hom-equiv-dependent-sequential-diagram =
    coh-equiv-dependent-sequential-diagram
```

### The predicate on morphisms of dependent sequential daigrams of being an equivalence

```agda
module _
  {l1 l2 l3 : Level} {A : sequential-diagram l1}
  {B : dependent-sequential-diagram A l2}
  (C : dependent-sequential-diagram A l3)
  where

  is-equiv-hom-dependent-sequential-diagram :
    hom-dependent-sequential-diagram B C → UU (l1 ⊔ l2 ⊔ l3)
  is-equiv-hom-dependent-sequential-diagram h =
    (n : ℕ) (a : family-sequential-diagram A n) →
    is-equiv (map-hom-dependent-sequential-diagram C h n a)

  is-equiv-hom-equiv-dependent-sequential-diagram :
    (e : equiv-dependent-sequential-diagram B C) →
    is-equiv-hom-dependent-sequential-diagram
      ( hom-equiv-dependent-sequential-diagram C e)
  is-equiv-hom-equiv-dependent-sequential-diagram e =
    is-equiv-map-equiv-dependent-sequential-diagram C e
```

### The identity equivalence of dependent sequential diagrams

```agda
module _
  {l1 l2 : Level} {A : sequential-diagram l1}
  (B : dependent-sequential-diagram A l2)
  where

  id-equiv-dependent-sequential-diagram : equiv-dependent-sequential-diagram B B
  pr1 id-equiv-dependent-sequential-diagram n a = id-equiv
  pr2 id-equiv-dependent-sequential-diagram n a = refl-htpy
```

### Composition of equivalences of dependent sequential diagrams

```agda
module _
  {l1 l2 l3 l4 : Level} {A : sequential-diagram l1}
  (B : dependent-sequential-diagram A l2)
  (C : dependent-sequential-diagram A l3)
  (D : dependent-sequential-diagram A l4)
  (f : equiv-dependent-sequential-diagram C D)
  (e : equiv-dependent-sequential-diagram B C)
  where

  comp-equiv-dependent-sequential-diagram :
    equiv-dependent-sequential-diagram B D
  pr1 comp-equiv-dependent-sequential-diagram n a =
    equiv-equiv-dependent-sequential-diagram D f n a ∘e
    equiv-equiv-dependent-sequential-diagram C e n a
  pr2 comp-equiv-dependent-sequential-diagram n a =
    pasting-horizontal-coherence-square-maps
      ( map-equiv-dependent-sequential-diagram C e n a)
      ( map-equiv-dependent-sequential-diagram D f n a)
      ( map-dependent-sequential-diagram B n a)
      ( map-dependent-sequential-diagram C n a)
      ( map-dependent-sequential-diagram D n a)
      ( map-equiv-dependent-sequential-diagram C e (succ-ℕ n) (map-sequential-diagram A n a))
      ( map-equiv-dependent-sequential-diagram D f (succ-ℕ n) (map-sequential-diagram A n a))
      ( coh-equiv-dependent-sequential-diagram C e n a)
      ( coh-equiv-dependent-sequential-diagram D f n a)
```

### The inverse of an equivalence of dependent sequential diagrams

```agda
module _
  {l1 l2 l3 : Level} {A : sequential-diagram l1}
  {B : dependent-sequential-diagram A l2}
  (C : dependent-sequential-diagram A l3)
  where

  inv-equiv-dependent-sequential-diagram :
    equiv-dependent-sequential-diagram B C →
    equiv-dependent-sequential-diagram C B
  pr1 (inv-equiv-dependent-sequential-diagram e) n a =
    inv-equiv (equiv-equiv-dependent-sequential-diagram C e n a)
  pr2 (inv-equiv-dependent-sequential-diagram e) n a =
    horizontal-inv-equiv-coherence-square-maps
      ( equiv-equiv-dependent-sequential-diagram C e n a)
      ( map-dependent-sequential-diagram B n a)
      ( map-dependent-sequential-diagram C n a)
      ( equiv-equiv-dependent-sequential-diagram C e
        ( succ-ℕ n)
        ( map-sequential-diagram A n a))
      ( coh-equiv-dependent-sequential-diagram C e n a)
```

## Properties

### Morphisms of dependent sequential diagrams which are equivalences are equivalences of dependent sequential diagrams

To construct an equivalence of dependent sequential diagrams `e : B ≃ C`, it
suffices to construct a morphism `h : B → C` and a proof that the maps `hₙ` are
fiberwise equivalences.

```agda
module _
  {l1 l2 l3 : Level} {A : sequential-diagram l1}
  {B : dependent-sequential-diagram A l2}
  (C : dependent-sequential-diagram A l3)
  (h : hom-dependent-sequential-diagram B C)
  where

  equiv-hom-dependent-sequential-diagram :
    is-equiv-hom-dependent-sequential-diagram C h →
    equiv-dependent-sequential-diagram B C
  pr1 (equiv-hom-dependent-sequential-diagram is-equiv-map) n a =
    (map-hom-dependent-sequential-diagram C h n a , is-equiv-map n a)
  pr2 (equiv-hom-dependent-sequential-diagram is-equiv-map) =
    coh-hom-dependent-sequential-diagram C h
```

### Characterization of identity types of dependent sequential diagrams

The type of equivalences of dependent sequential diagrams characterizes the
identity type of dependent sequential diagrams.

```agda
module _
  {l1 l2 : Level} {A : sequential-diagram l1}
  (B : dependent-sequential-diagram A l2)
  where

  equiv-eq-dependent-sequential-diagram :
    (C : dependent-sequential-diagram A l2) →
    (B ＝ C) → equiv-dependent-sequential-diagram B C
  equiv-eq-dependent-sequential-diagram .B refl =
    id-equiv-dependent-sequential-diagram B

  abstract
    is-torsorial-equiv-dependent-sequential-diagram :
      is-torsorial (equiv-dependent-sequential-diagram {l3 = l2} B)
    is-torsorial-equiv-dependent-sequential-diagram =
      is-torsorial-Eq-structure
        ( is-torsorial-Eq-Π
          ( λ n →
            is-torsorial-Eq-Π
              ( λ a →
                is-torsorial-equiv
                  ( family-dependent-sequential-diagram B n a))))
        ( family-dependent-sequential-diagram B , λ n a → id-equiv)
        ( is-torsorial-Eq-Π
          ( λ n →
            is-torsorial-Eq-Π
              ( λ a →
                is-torsorial-htpy (map-dependent-sequential-diagram B n a))))

  is-equiv-equiv-eq-dependent-sequential-diagram :
    (C : dependent-sequential-diagram A l2) →
    is-equiv (equiv-eq-dependent-sequential-diagram C)
  is-equiv-equiv-eq-dependent-sequential-diagram =
    fundamental-theorem-id
      ( is-torsorial-equiv-dependent-sequential-diagram)
      ( equiv-eq-dependent-sequential-diagram)

  extensionality-dependent-sequential-diagram :
    (C : dependent-sequential-diagram A l2) →
    (B ＝ C) ≃ equiv-dependent-sequential-diagram B C
  pr1 (extensionality-dependent-sequential-diagram C) =
    equiv-eq-dependent-sequential-diagram C
  pr2 (extensionality-dependent-sequential-diagram C) =
    is-equiv-equiv-eq-dependent-sequential-diagram C

  eq-equiv-dependent-sequential-diagram :
    (C : dependent-sequential-diagram A l2) →
    equiv-dependent-sequential-diagram B C → (B ＝ C)
  eq-equiv-dependent-sequential-diagram C =
    map-inv-equiv (extensionality-dependent-sequential-diagram C)
```
