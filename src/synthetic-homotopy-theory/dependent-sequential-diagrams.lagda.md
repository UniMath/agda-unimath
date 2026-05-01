# Dependent sequential diagrams

```agda
module synthetic-homotopy-theory.dependent-sequential-diagrams where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.homotopies
open import foundation.universe-levels

open import synthetic-homotopy-theory.sequential-diagrams
```

</details>

## Idea

A **dependent sequential diagram** over a
[sequential diagram](synthetic-homotopy-theory.sequential-diagrams.md) `(A, a)`
is a [sequence](lists.dependent-sequences.md) of families of types
`B : (n : ℕ) → Aₙ → 𝒰` over the types in the base sequential diagram, equipped
with fiberwise maps

```text
bₙ : (x : Aₙ) → Bₙ x → Bₙ₊₁ (aₙ x).
```

They can be thought of as a family of sequential diagrams

```text
       bₙ(x)           bₙ₊₁(aₙ(x))
 Bₙ(x) ----> Bₙ₊₁(aₙ(x)) -------> Bₙ₊₂(aₙ₊₁(aₙ(x))) ----> ⋯,
```

one for each `x : Aₙ`, or as a sequence fibered over `(A, a)`, visualized as

```text
     b₀      b₁      b₂
 B₀ ---> B₁ ---> B₂ ---> ⋯
 |       |       |
 |       |       |
 ↡       ↡       ↡
 A₀ ---> A₁ ---> A₂ ---> ⋯.
     a₀      a₁      a₂
```

## Definitions

### Dependent sequential diagrams

```agda
dependent-sequential-diagram :
  { l1 : Level} → (A : sequential-diagram l1) →
  ( l2 : Level) → UU (l1 ⊔ lsuc l2)
dependent-sequential-diagram A l2 =
  Σ ( ( n : ℕ) → family-sequential-diagram A n → UU l2)
    ( λ B →
      ( n : ℕ) (x : family-sequential-diagram A n) →
      B n x → B (succ-ℕ n) (map-sequential-diagram A n x))
```

### Components of a dependent sequential diagram

```agda
module _
  { l1 l2 : Level} {A : sequential-diagram l1}
  ( B : dependent-sequential-diagram A l2)
  where

  family-dependent-sequential-diagram :
    ( n : ℕ) → family-sequential-diagram A n → UU l2
  family-dependent-sequential-diagram = pr1 B

  map-dependent-sequential-diagram :
    ( n : ℕ) (x : family-sequential-diagram A n) →
    family-dependent-sequential-diagram n x →
    family-dependent-sequential-diagram
      ( succ-ℕ n)
      ( map-sequential-diagram A n x)
  map-dependent-sequential-diagram = pr2 B
```

### Constant dependent sequential diagrams

Constant dependent sequential diagrams are dependent sequential diagrams where
the dependent type family `B` is [constant](foundation.constant-maps.md).

```agda
module _
  { l1 l2 : Level} (A : sequential-diagram l1) (B : sequential-diagram l2)
  where

  constant-dependent-sequential-diagram : dependent-sequential-diagram A l2
  pr1 constant-dependent-sequential-diagram n _ = family-sequential-diagram B n
  pr2 constant-dependent-sequential-diagram n _ = map-sequential-diagram B n
```

### Sections of dependent sequential diagrams

A **section of a dependent sequential diagram** `(B, b)` is a
[sequence](lists.dependent-sequences.md) of sections `sₙ : (x : Aₙ) → Bₙ(x)`
satisfying the naturality condition that all squares of the form

```text
          bₙ(x)
  Bₙ(x) -------> Bₙ₊₁(aₙ(x))
    ∧                ∧
 sₙ |                | sₙ₊₁
    |                |
 (x : Aₙ) ---> (aₙ(x) : Aₙ₊₁)
           aₙ
```

[commute](foundation.commuting-squares-of-maps.md).

```agda
module _
  { l1 l2 : Level} (A : sequential-diagram l1)
  ( B : dependent-sequential-diagram A l2)
  where

  naturality-section-dependent-sequential-diagram :
    ( s :
      ( n : ℕ) (x : family-sequential-diagram A n) →
      family-dependent-sequential-diagram B n x) →
    UU (l1 ⊔ l2)
  naturality-section-dependent-sequential-diagram s =
    ( n : ℕ) →
    ( map-dependent-sequential-diagram B n _ ∘ s n) ~
    ( s (succ-ℕ n) ∘ map-sequential-diagram A n)

  section-dependent-sequential-diagram : UU (l1 ⊔ l2)
  section-dependent-sequential-diagram =
    Σ ( ( n : ℕ) (x : family-sequential-diagram A n) →
        family-dependent-sequential-diagram B n x)
      ( λ s → naturality-section-dependent-sequential-diagram s)
```

### Components of sections of dependent sequential diagrams

```agda
module _
  { l1 l2 : Level} (A : sequential-diagram l1)
  ( B : dependent-sequential-diagram A l2)
  ( s : section-dependent-sequential-diagram A B)
  where

  map-section-dependent-sequential-diagram :
    ( n : ℕ) (x : family-sequential-diagram A n) →
    family-dependent-sequential-diagram B n x
  map-section-dependent-sequential-diagram = pr1 s

  naturality-map-section-dependent-sequential-diagram :
    naturality-section-dependent-sequential-diagram A B
      map-section-dependent-sequential-diagram
  naturality-map-section-dependent-sequential-diagram = pr2 s
```

## References

{{#bibliography}} {{#reference SvDR20}}
