# Towers of types

```agda
module foundation.towers-of-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.constant-maps
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.homotopies
open import foundation.iterating-functions
open import foundation.sequences
open import foundation.unit-type
open import foundation.universe-levels

open import structured-types.pointed-maps
open import structured-types.pointed-types
```

</details>

## Idea

A **tower** of types `f` is a [sequence](foundation.sequences.md) of types
together with a map between every two consecutive types

```text
  fₙ : Xₙ₊₁ → Xₙ
```

Giving an sequence of maps that extend infinitely to the left:

```text
     f₃      f₂      f₁      f₀
  ⋯ ---> X₃ ---> X₂ ---> X₁ ---> X₀.
```

## Definitions

### Towers of types

```agda
sequence-map-Tower : {l : Level} → (ℕ → UU l) → UU l
sequence-map-Tower A = (n : ℕ) → A (succ-ℕ n) → A n

Tower : (l : Level) → UU (lsuc l)
Tower l = Σ (ℕ → UU l) (sequence-map-Tower)

type-Tower : {l : Level} → Tower l → ℕ → UU l
type-Tower = pr1

map-Tower :
  {l : Level} (A : Tower l) (n : ℕ) → type-Tower A (succ-ℕ n) → type-Tower A n
map-Tower = pr2
```

### Composites in towers

```agda
comp-map-Tower :
  {l : Level} (A : Tower l) (n r : ℕ) → type-Tower A (n +ℕ r) → type-Tower A n
comp-map-Tower A n zero-ℕ = id
comp-map-Tower A n (succ-ℕ r) = comp-map-Tower A n r ∘ map-Tower A (n +ℕ r)
```

## Dependent towers of types

```agda
sequence-map-Dependent-Tower :
  {l1 l2 : Level} (A : Tower l1) →
  ((n : ℕ) → type-Tower A n → UU l2) → UU (l1 ⊔ l2)
sequence-map-Dependent-Tower A B =
  (n : ℕ) (x : type-Tower A (succ-ℕ n)) → B (succ-ℕ n) x → B n (map-Tower A n x)

Dependent-Tower : {l1 : Level} (l2 : Level) (A : Tower l1) → UU (l1 ⊔ lsuc l2)
Dependent-Tower l2 A =
  Σ ((n : ℕ) → type-Tower A n → UU l2) (sequence-map-Dependent-Tower A)

family-Dependent-Tower :
  {l1 l2 : Level} {A : Tower l1} →
  Dependent-Tower l2 A → ((n : ℕ) → type-Tower A n → UU l2)
family-Dependent-Tower = pr1

map-Dependent-Tower :
  {l1 l2 : Level} {A : Tower l1} (B : Dependent-Tower l2 A) →
  (n : ℕ) (x : type-Tower A (succ-ℕ n)) →
  family-Dependent-Tower B (succ-ℕ n) x →
  family-Dependent-Tower B n (map-Tower A n x)
map-Dependent-Tower = pr2
```

### Composites in dependent towers

```agda
comp-map-Dependent-Tower :
  {l1 l2 : Level} {A : Tower l1} (B : Dependent-Tower l2 A)
  (n r : ℕ) (x : type-Tower A (n +ℕ r)) →
  family-Dependent-Tower B (n +ℕ r) x →
  family-Dependent-Tower B n (comp-map-Tower A n r x)
comp-map-Dependent-Tower B n zero-ℕ x y = y
comp-map-Dependent-Tower {A = A} B n (succ-ℕ r) x y =
  comp-map-Dependent-Tower B n r
    ( map-Tower A (n +ℕ r) x)
    ( map-Dependent-Tower B (n +ℕ r) x y)
```

### Constant dependent towers of types

```agda
const-Dependent-Tower :
    {l1 l2 : Level} (A : Tower l1) → Tower l2 → Dependent-Tower l2 A
pr1 (const-Dependent-Tower A B) n _ = type-Tower B n
pr2 (const-Dependent-Tower A B) n _ = map-Tower B n
```

### Sections of a dependent tower

A **section of a dependent tower** `B` over `A` is a commuting diagram of the
form

```text
  ⋯ ----> Aₙ₊₁ ----> Aₙ ----> ⋯ ----> A₁ ----> A₀
           |         |               |        |
  ⋯        |         |       ⋯       |        |
           v         v               v        v
  ⋯ ----> Bₙ₊₁ ----> Bₙ ----> ⋯ ----> B₁ ----> B₀.
```

```agda
section-Dependent-Tower :
  {l1 l2 : Level} (A : Tower l1) (B : Dependent-Tower l2 A) → UU (l1 ⊔ l2)
section-Dependent-Tower A B =
  Σ ( (n : ℕ) (x : type-Tower A n) → family-Dependent-Tower B n x)
    ( λ s →
      (n : ℕ) → s n ∘ map-Tower A n ~ map-Dependent-Tower B n _ ∘ s (succ-ℕ n))
```

## Operations

### Right shifting a tower

We can **right shift** a tower of types by forgetting the first terms.

```agda
right-shift-Tower : {l : Level} → Tower l → Tower l
pr1 (right-shift-Tower A) n = type-Tower A (succ-ℕ n)
pr2 (right-shift-Tower A) n = map-Tower A (succ-ℕ n)

iterated-right-shift-Tower : {l : Level} (n : ℕ) → Tower l → Tower l
iterated-right-shift-Tower n = iterate n right-shift-Tower
```

### Left shifting a tower

We can **left shift** a tower of types by padding it with the
[terminal type](foundation-core.unit-type.md) `unit`.

```agda
left-shift-Tower : {l : Level} → Tower l → Tower l
pr1 (left-shift-Tower {l} A) zero-ℕ = raise-unit l
pr1 (left-shift-Tower A) (succ-ℕ n) = type-Tower A n
pr2 (left-shift-Tower A) zero-ℕ = raise-terminal-map
pr2 (left-shift-Tower A) (succ-ℕ n) = map-Tower A n

iterated-left-shift-Tower : {l : Level} (n : ℕ) → Tower l → Tower l
iterated-left-shift-Tower n = iterate n left-shift-Tower
```
