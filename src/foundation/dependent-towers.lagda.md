# Dependent towers of types

```agda
module foundation.dependent-towers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.towers
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.homotopies
```

</details>

## Idea

A **dependent tower** `B` over a base [tower](foundation.towers.md) `A` is a
[sequence](foundation.sequences.md) of families over each `Aₙ` together with
maps of fibers

```text
  gₙ : (xₙ₊₁ : Aₙ₊₁) → Bₙ₊₁(xₙ₊₁) → Bₙ(fₙ(xₙ₊₁)),
```

where `f` is the sequence of maps of the base tower, giving a dependent
sequential diagram of maps that extend infinitely to the left:

```text
     g₃      g₂      g₁      g₀
  ⋯ ---> B₃ ---> B₂ ---> B₁ ---> B₀.
```

## Definitions

### Dependent towers of types

```agda
sequence-map-dependent-tower :
  {l1 l2 : Level} (A : tower l1) →
  ((n : ℕ) → type-tower A n → UU l2) → UU (l1 ⊔ l2)
sequence-map-dependent-tower A B =
  (n : ℕ) (x : type-tower A (succ-ℕ n)) → B (succ-ℕ n) x → B n (map-tower A n x)

dependent-tower : {l1 : Level} (l2 : Level) (A : tower l1) → UU (l1 ⊔ lsuc l2)
dependent-tower l2 A =
  Σ ((n : ℕ) → type-tower A n → UU l2) (sequence-map-dependent-tower A)

family-dependent-tower :
  {l1 l2 : Level} {A : tower l1} →
  dependent-tower l2 A → ((n : ℕ) → type-tower A n → UU l2)
family-dependent-tower = pr1

map-dependent-tower :
  {l1 l2 : Level} {A : tower l1} (B : dependent-tower l2 A) →
  (n : ℕ) (x : type-tower A (succ-ℕ n)) →
  family-dependent-tower B (succ-ℕ n) x →
  family-dependent-tower B n (map-tower A n x)
map-dependent-tower = pr2
```

### Constant dependent towers of types

```agda
const-dependent-tower :
    {l1 l2 : Level} (A : tower l1) → tower l2 → dependent-tower l2 A
pr1 (const-dependent-tower A B) n _ = type-tower B n
pr2 (const-dependent-tower A B) n _ = map-tower B n
```

### Sections of a dependent tower

A **section of a dependent tower** `(B , g)` over `(A , f)` is a choice of
sections `hₙ` of each `Bₙ` that vary naturally over `A`, by which we mean that
the diagrams

```text
          gₙ
    Bₙ₊₁ ---> Bₙ
    ^         ^
hₙ₊₁|         | hₙ
    |         |
    Aₙ₊₁ ---> Aₙ
          fₙ
```

commute for each `n : ℕ`.

```agda
module _
  {l1 l2 : Level} (A : tower l1) (B : dependent-tower l2 A)
  where

  naturality-section-dependent-tower :
    (h : (n : ℕ) (x : type-tower A n) → family-dependent-tower B n x)
    (n : ℕ) → UU (l1 ⊔ l2)
  naturality-section-dependent-tower h n =
    h n ∘ map-tower A n ~ map-dependent-tower B n _ ∘ h (succ-ℕ n)

  section-dependent-tower : UU (l1 ⊔ l2)
  section-dependent-tower =
    Σ ( (n : ℕ) (x : type-tower A n) → family-dependent-tower B n x)
      ( λ h → (n : ℕ) → naturality-section-dependent-tower h n)

  map-section-dependent-tower :
    section-dependent-tower →
    (n : ℕ) (x : type-tower A n) → family-dependent-tower B n x
  map-section-dependent-tower = pr1

  naturality-map-section-dependent-tower :
    (f : section-dependent-tower) (n : ℕ) →
    naturality-section-dependent-tower (map-section-dependent-tower f) n
  naturality-map-section-dependent-tower = pr2
```

## Operations

### Right shifting a dependent tower

We can **right shift** a dependent tower of types by forgetting the first terms.

```agda
right-shift-dependent-tower :
  {l1 l2 : Level} {A : tower l1} →
  dependent-tower l2 A → dependent-tower l2 (right-shift-tower A)
pr1 (right-shift-dependent-tower B) n = family-dependent-tower B (succ-ℕ n)
pr2 (right-shift-dependent-tower B) n = map-dependent-tower B (succ-ℕ n)
```

### Left shifting a dependent tower

We can **left shift** a dependent tower of types by padding it with the
[terminal type](foundation.unit-type.md) `unit`.

```agda
left-shift-dependent-tower :
    {l1 l2 : Level} {A : tower l1} →
  dependent-tower l2 A → dependent-tower l2 (left-shift-tower A)
pr1 (left-shift-dependent-tower {l2 = l2} B) zero-ℕ x = raise-unit l2
pr1 (left-shift-dependent-tower B) (succ-ℕ n) = family-dependent-tower B n
pr2 (left-shift-dependent-tower B) zero-ℕ _ = raise-terminal-map
pr2 (left-shift-dependent-tower B) (succ-ℕ n) = map-dependent-tower B n
```
