# Inverse sequential diagrams of types

```agda
module foundation.inverse-sequential-diagrams where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.iterating-functions
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

An
{{#concept "inverse sequential diagram" Disambiguation="types" Agda=inverse-sequential-diagram}}
of types `A` is a [sequence](lists.sequences.md) of types together with maps
between every two consecutive types

```text
  fₙ : Aₙ₊₁ → Aₙ
```

giving a sequential diagram of maps that extend infinitely to the left:

```text
     f₃      f₂      f₁      f₀
  ⋯ ---> A₃ ---> A₂ ---> A₁ ---> A₀.
```

This is in contrast to the notion of
[sequential diagram](synthetic-homotopy-theory.sequential-diagrams.md), which
extend infinitely to the right, hence is the formal dual to inverse sequential
diagrams.

## Definitions

### Inverse sequential diagrams of types

```agda
sequence-map-inverse-sequential-diagram : {l : Level} → (ℕ → UU l) → UU l
sequence-map-inverse-sequential-diagram A = (n : ℕ) → A (succ-ℕ n) → A n

inverse-sequential-diagram : (l : Level) → UU (lsuc l)
inverse-sequential-diagram l =
  Σ (ℕ → UU l) (sequence-map-inverse-sequential-diagram)

family-inverse-sequential-diagram :
  {l : Level} → inverse-sequential-diagram l → ℕ → UU l
family-inverse-sequential-diagram = pr1

map-inverse-sequential-diagram :
  {l : Level} (A : inverse-sequential-diagram l) (n : ℕ) →
  family-inverse-sequential-diagram A (succ-ℕ n) →
  family-inverse-sequential-diagram A n
map-inverse-sequential-diagram = pr2
```

## Operations

### Right shifting an inverse sequential diagram

We can **right shift** an inverse sequential diagram of types by forgetting the
first terms.

```agda
right-shift-inverse-sequential-diagram :
  {l : Level} → inverse-sequential-diagram l → inverse-sequential-diagram l
pr1 (right-shift-inverse-sequential-diagram A) n =
  family-inverse-sequential-diagram A (succ-ℕ n)
pr2 (right-shift-inverse-sequential-diagram A) n =
  map-inverse-sequential-diagram A (succ-ℕ n)

iterated-right-shift-inverse-sequential-diagram :
  {l : Level} → ℕ → inverse-sequential-diagram l → inverse-sequential-diagram l
iterated-right-shift-inverse-sequential-diagram n =
  iterate n right-shift-inverse-sequential-diagram
```

### Left shifting an inverse sequential diagram

We can **left shift** an inverse sequential diagram of types by padding it with
the [terminal type](foundation.unit-type.md) `unit`.

```agda
left-shift-inverse-sequential-diagram :
  {l : Level} → inverse-sequential-diagram l → inverse-sequential-diagram l
pr1 (left-shift-inverse-sequential-diagram {l} A) 0 = raise-unit l
pr1 (left-shift-inverse-sequential-diagram A) (succ-ℕ n) =
  family-inverse-sequential-diagram A n
pr2 (left-shift-inverse-sequential-diagram A) 0 =
  raise-terminal-map (family-inverse-sequential-diagram A 0)
pr2 (left-shift-inverse-sequential-diagram A) (succ-ℕ n) =
  map-inverse-sequential-diagram A n

iterated-left-shift-inverse-sequential-diagram :
  {l : Level} (n : ℕ) →
  inverse-sequential-diagram l → inverse-sequential-diagram l
iterated-left-shift-inverse-sequential-diagram n =
  iterate n left-shift-inverse-sequential-diagram
```

### Postcomposition inverse sequential diagrams

Given an inverse sequential diagram `A` and a type `X` there is an inverse
sequential diagram `X → A` defined by levelwise postcomposition

```text
                    (f₂ ∘ -)          (f₁ ∘ -)          (f₀ ∘ -)
  ⋯ -----> (X → A₃) -------> (X → A₂) -------> (X → A₁) -------> (X → A₀).
```

```agda
module _
  {l1 l2 : Level} (X : UU l1) (A : inverse-sequential-diagram l2)
  where

  postcomp-inverse-sequential-diagram : inverse-sequential-diagram (l1 ⊔ l2)
  pr1 postcomp-inverse-sequential-diagram n =
    X → family-inverse-sequential-diagram A n
  pr2 postcomp-inverse-sequential-diagram n g x =
    map-inverse-sequential-diagram A n (g x)
```

## Table of files about sequential limits

The following table lists files that are about sequential limits as a general
concept.

{{#include tables/sequential-limits.md}}
