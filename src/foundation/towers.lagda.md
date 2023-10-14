# Towers of types

```agda
module foundation.towers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.iterating-functions
open import foundation.structure-identity-principle
open import foundation.unit-type
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.homotopies
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

### Composites in towers

```agda
comp-map-tower :
  {l : Level} (A : tower l) (n r : ℕ) → type-tower A (n +ℕ r) → type-tower A n
comp-map-tower A n zero-ℕ = id
comp-map-tower A n (succ-ℕ r) = comp-map-tower A n r ∘ map-tower A (n +ℕ r)
```

## Dependent towers of types

```agda
sequence-map-Dependent-tower :
  {l1 l2 : Level} (A : tower l1) →
  ((n : ℕ) → type-tower A n → UU l2) → UU (l1 ⊔ l2)
sequence-map-Dependent-tower A B =
  (n : ℕ) (x : type-tower A (succ-ℕ n)) → B (succ-ℕ n) x → B n (map-tower A n x)

Dependent-tower : {l1 : Level} (l2 : Level) (A : tower l1) → UU (l1 ⊔ lsuc l2)
Dependent-tower l2 A =
  Σ ((n : ℕ) → type-tower A n → UU l2) (sequence-map-Dependent-tower A)

family-Dependent-tower :
  {l1 l2 : Level} {A : tower l1} →
  Dependent-tower l2 A → ((n : ℕ) → type-tower A n → UU l2)
family-Dependent-tower = pr1

map-Dependent-tower :
  {l1 l2 : Level} {A : tower l1} (B : Dependent-tower l2 A) →
  (n : ℕ) (x : type-tower A (succ-ℕ n)) →
  family-Dependent-tower B (succ-ℕ n) x →
  family-Dependent-tower B n (map-tower A n x)
map-Dependent-tower = pr2
```

### Composites in dependent towers

```agda
comp-map-Dependent-tower :
  {l1 l2 : Level} {A : tower l1} (B : Dependent-tower l2 A)
  (n r : ℕ) (x : type-tower A (n +ℕ r)) →
  family-Dependent-tower B (n +ℕ r) x →
  family-Dependent-tower B n (comp-map-tower A n r x)
comp-map-Dependent-tower B n zero-ℕ x y = y
comp-map-Dependent-tower {A = A} B n (succ-ℕ r) x y =
  comp-map-Dependent-tower B n r
    ( map-tower A (n +ℕ r) x)
    ( map-Dependent-tower B (n +ℕ r) x y)
```

### Constant dependent towers of types

```agda
const-Dependent-tower :
    {l1 l2 : Level} (A : tower l1) → tower l2 → Dependent-tower l2 A
pr1 (const-Dependent-tower A B) n _ = type-tower B n
pr2 (const-Dependent-tower A B) n _ = map-tower B n
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
naturality-section-Dependent-tower :
  {l1 l2 : Level} (A : tower l1) (B : Dependent-tower l2 A)
  (h : (n : ℕ) (x : type-tower A n) → family-Dependent-tower B n x) (n : ℕ) →
  UU (l1 ⊔ l2)
naturality-section-Dependent-tower A B h n =
  h n ∘ map-tower A n ~ map-Dependent-tower B n _ ∘ h (succ-ℕ n)

section-Dependent-tower :
  {l1 l2 : Level} (A : tower l1) (B : Dependent-tower l2 A) → UU (l1 ⊔ l2)
section-Dependent-tower A B =
  Σ ( (n : ℕ) (x : type-tower A n) → family-Dependent-tower B n x)
    ( λ h → (n : ℕ) → naturality-section-Dependent-tower A B h n)
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
