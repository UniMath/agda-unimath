# Towers of types

```agda
module foundation.towers where
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

A **tower of types** `f` is a [sequence](foundation.sequences.md) of types
together with maps between every two consecutive types

```text
  fₙ : Aₙ₊₁ → Aₙ
```

giving a sequential diagram of maps that extend infinitely to the left:

```text
     f₃      f₂      f₁      f₀
  ⋯ ---> A₃ ---> A₂ ---> A₁ ---> A₀.
```

## Definitions

### Towers of types

```agda
sequence-map-tower : {l : Level} → (ℕ → UU l) → UU l
sequence-map-tower A = (n : ℕ) → A (succ-ℕ n) → A n

tower : (l : Level) → UU (lsuc l)
tower l = Σ (ℕ → UU l) (sequence-map-tower)

type-tower : {l : Level} → tower l → ℕ → UU l
type-tower = pr1

map-tower :
  {l : Level} (A : tower l) (n : ℕ) → type-tower A (succ-ℕ n) → type-tower A n
map-tower = pr2
```

## Operations

### Right shifting a tower

We can **right shift** a tower of types by forgetting the first terms.

```agda
right-shift-tower : {l : Level} → tower l → tower l
pr1 (right-shift-tower A) n = type-tower A (succ-ℕ n)
pr2 (right-shift-tower A) n = map-tower A (succ-ℕ n)

iterated-right-shift-tower : {l : Level} (n : ℕ) → tower l → tower l
iterated-right-shift-tower n = iterate n right-shift-tower
```

### Left shifting a tower

We can **left shift** a tower of types by padding it with the
[terminal type](foundation.unit-type.md) `unit`.

```agda
left-shift-tower : {l : Level} → tower l → tower l
pr1 (left-shift-tower {l} A) zero-ℕ = raise-unit l
pr1 (left-shift-tower A) (succ-ℕ n) = type-tower A n
pr2 (left-shift-tower A) zero-ℕ = raise-terminal-map
pr2 (left-shift-tower A) (succ-ℕ n) = map-tower A n

iterated-left-shift-tower : {l : Level} (n : ℕ) → tower l → tower l
iterated-left-shift-tower n = iterate n left-shift-tower
```

## Table of files about sequential limits

The following table lists files that are about sequential limits as a general
concept.

{{#include tables/sequential-limits.md}}
