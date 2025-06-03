# Dependent inverse sequential diagrams of types

```agda
module foundation.dependent-inverse-sequential-diagrams where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.inverse-sequential-diagrams
open import foundation.iterating-families-of-maps
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.homotopies
```

</details>

## Idea

A **dependent inverse sequential diagram** `B` over a base
[inverse sequential diagram](foundation.inverse-sequential-diagrams.md) `A` is a
[sequence](lists.sequences.md) of families over each `Aₙ` together with maps of
fibers

```text
  gₙ : (xₙ₊₁ : Aₙ₊₁) → Bₙ₊₁(xₙ₊₁) → Bₙ(fₙ(xₙ₊₁)),
```

where `f` is the sequence of maps of the base inverse sequential diagram, giving
a dependent sequential diagram of maps that extend infinitely to the left:

```text
     g₃      g₂      g₁      g₀
  ⋯ ---> B₃ ---> B₂ ---> B₁ ---> B₀.
```

## Definitions

### Dependent inverse sequential diagrams of types

```agda
sequence-map-dependent-inverse-sequential-diagram :
  {l1 l2 : Level} (A : inverse-sequential-diagram l1) →
  ((n : ℕ) → family-inverse-sequential-diagram A n → UU l2) → UU (l1 ⊔ l2)
sequence-map-dependent-inverse-sequential-diagram A B =
  (n : ℕ) (x : family-inverse-sequential-diagram A (succ-ℕ n)) →
  B (succ-ℕ n) x → B n (map-inverse-sequential-diagram A n x)

dependent-inverse-sequential-diagram :
  {l1 : Level} (l2 : Level) (A : inverse-sequential-diagram l1) →
  UU (l1 ⊔ lsuc l2)
dependent-inverse-sequential-diagram l2 A =
  Σ ( (n : ℕ) → family-inverse-sequential-diagram A n → UU l2)
    ( sequence-map-dependent-inverse-sequential-diagram A)

family-dependent-inverse-sequential-diagram :
  {l1 l2 : Level} {A : inverse-sequential-diagram l1} →
  dependent-inverse-sequential-diagram l2 A →
  (n : ℕ) → family-inverse-sequential-diagram A n → UU l2
family-dependent-inverse-sequential-diagram = pr1

map-dependent-inverse-sequential-diagram :
  {l1 l2 : Level} {A : inverse-sequential-diagram l1}
  (B : dependent-inverse-sequential-diagram l2 A) →
  (n : ℕ) (x : family-inverse-sequential-diagram A (succ-ℕ n)) →
  family-dependent-inverse-sequential-diagram B (succ-ℕ n) x →
  family-dependent-inverse-sequential-diagram B n
    ( map-inverse-sequential-diagram A n x)
map-dependent-inverse-sequential-diagram = pr2
```

### Constant dependent inverse sequential diagrams of types

```agda
const-dependent-inverse-sequential-diagram :
  {l1 l2 : Level}
  (A : inverse-sequential-diagram l1) → inverse-sequential-diagram l2 →
  dependent-inverse-sequential-diagram l2 A
pr1 (const-dependent-inverse-sequential-diagram A B) n _ =
  family-inverse-sequential-diagram B n
pr2 (const-dependent-inverse-sequential-diagram A B) n _ =
  map-inverse-sequential-diagram B n
```

### Sections of a dependent inverse sequential diagram

A **section of a dependent inverse sequential diagram `(B , g)` over `(A , f)`**
is a choice of sections `hₙ` of each `Bₙ` that vary naturally over `A`, by which
we mean that the diagrams

```text
            gₙ
      Bₙ₊₁ ---> Bₙ
      ∧         ∧
  hₙ₊₁|         | hₙ
      |         |
      Aₙ₊₁ ---> Aₙ
            fₙ
```

commute for each `n : ℕ`.

```agda
module _
  {l1 l2 : Level} (A : inverse-sequential-diagram l1)
  (B : dependent-inverse-sequential-diagram l2 A)
  where

  naturality-section-dependent-inverse-sequential-diagram :
    (h :
      (n : ℕ) (x : family-inverse-sequential-diagram A n) →
      family-dependent-inverse-sequential-diagram B n x) →
    UU (l1 ⊔ l2)
  naturality-section-dependent-inverse-sequential-diagram h =
    ( n : ℕ) →
    h n ∘ map-inverse-sequential-diagram A n ~
    map-dependent-inverse-sequential-diagram B n _ ∘ h (succ-ℕ n)

  section-dependent-inverse-sequential-diagram : UU (l1 ⊔ l2)
  section-dependent-inverse-sequential-diagram =
    Σ ( (n : ℕ) (x : family-inverse-sequential-diagram A n) →
        family-dependent-inverse-sequential-diagram B n x)
      ( naturality-section-dependent-inverse-sequential-diagram)

  map-section-dependent-inverse-sequential-diagram :
    section-dependent-inverse-sequential-diagram →
    (n : ℕ) (x : family-inverse-sequential-diagram A n) →
    family-dependent-inverse-sequential-diagram B n x
  map-section-dependent-inverse-sequential-diagram = pr1

  naturality-map-section-dependent-inverse-sequential-diagram :
    (f : section-dependent-inverse-sequential-diagram) →
    naturality-section-dependent-inverse-sequential-diagram
      ( map-section-dependent-inverse-sequential-diagram f)
  naturality-map-section-dependent-inverse-sequential-diagram = pr2
```

## Operations

### Right shifting a dependent inverse sequential diagram

We can **right shift** a dependent inverse sequential diagram of types by
forgetting the first terms.

```agda
right-shift-dependent-inverse-sequential-diagram :
  {l1 l2 : Level} {A : inverse-sequential-diagram l1} →
  dependent-inverse-sequential-diagram l2 A →
  dependent-inverse-sequential-diagram l2
    ( right-shift-inverse-sequential-diagram A)
pr1 (right-shift-dependent-inverse-sequential-diagram B) n =
  family-dependent-inverse-sequential-diagram B (succ-ℕ n)
pr2 (right-shift-dependent-inverse-sequential-diagram B) n =
  map-dependent-inverse-sequential-diagram B (succ-ℕ n)

iterated-right-shift-dependent-inverse-sequential-diagram :
  {l1 l2 : Level} (n : ℕ) →
  (A : inverse-sequential-diagram l1) →
  dependent-inverse-sequential-diagram l2 A →
  dependent-inverse-sequential-diagram l2
    ( iterated-right-shift-inverse-sequential-diagram n A)
iterated-right-shift-dependent-inverse-sequential-diagram n A =
  iterate-family-of-maps n
    ( λ A → right-shift-dependent-inverse-sequential-diagram {A = A})
    ( A)
```

### Left shifting a dependent inverse sequential diagram

We can **left shift** a dependent inverse sequential diagram of types by padding
it with the [terminal type](foundation.unit-type.md) `unit`.

```agda
left-shift-dependent-inverse-sequential-diagram :
    {l1 l2 : Level} {A : inverse-sequential-diagram l1} →
  dependent-inverse-sequential-diagram l2 A →
  dependent-inverse-sequential-diagram l2
    ( left-shift-inverse-sequential-diagram A)
pr1 (left-shift-dependent-inverse-sequential-diagram {l2 = l2} B) 0 x =
  raise-unit l2
pr1 (left-shift-dependent-inverse-sequential-diagram B) (succ-ℕ n) =
  family-dependent-inverse-sequential-diagram B n
pr2 (left-shift-dependent-inverse-sequential-diagram B) 0 x =
  raise-terminal-map (family-dependent-inverse-sequential-diagram B 0 x)
pr2 (left-shift-dependent-inverse-sequential-diagram B) (succ-ℕ n) =
  map-dependent-inverse-sequential-diagram B n

iterated-left-shift-dependent-inverse-sequential-diagram :
  {l1 l2 : Level} (n : ℕ) →
  (A : inverse-sequential-diagram l1) →
  dependent-inverse-sequential-diagram l2 A →
  dependent-inverse-sequential-diagram l2
    ( iterated-left-shift-inverse-sequential-diagram n A)
iterated-left-shift-dependent-inverse-sequential-diagram n A =
  iterate-family-of-maps n
    ( λ A → left-shift-dependent-inverse-sequential-diagram {A = A})
    ( A)
```

## Table of files about sequential limits

The following table lists files that are about sequential limits as a general
concept.

{{#include tables/sequential-limits.md}}
