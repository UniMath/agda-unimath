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
is a [sequence](foundation.dependent-sequences.md) of families of types
`B : (n : ℕ) → A n → 𝓤` over the types in the base sequential diagram, equipped
with fiberwise maps

```text
bₙ : (x : A n) → B n x → B (n + 1) (aₙ x).
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
  { l1 l2 : Level} (A : sequential-diagram l1)
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

```agda
module _
  { l1 l2 : Level} (A : sequential-diagram l1) (B : sequential-diagram l2)
  where

  constant-dependent-sequential-diagram : dependent-sequential-diagram A l2
  pr1 constant-dependent-sequential-diagram n _ = family-sequential-diagram B n
  pr2 constant-dependent-sequential-diagram n _ = map-sequential-diagram B n
```

### Sections of dependent sequential diagrams

```agda
module _
  { l1 l2 : Level} (A : sequential-diagram l1)
  ( B : dependent-sequential-diagram A l2)
  where

  naturality-section-dependent-sequential-diagram :
    ( s :
      ( n : ℕ) (x : family-sequential-diagram A n) →
      family-dependent-sequential-diagram A B n x) →
    UU (l1 ⊔ l2)
  naturality-section-dependent-sequential-diagram s =
    ( n : ℕ) →
    ( map-dependent-sequential-diagram A B n _ ∘ s n) ~
    ( s (succ-ℕ n) ∘ map-sequential-diagram A n)

  section-dependent-sequential-diagram : UU (l1 ⊔ l2)
  section-dependent-sequential-diagram =
    Σ ( ( n : ℕ) (x : family-sequential-diagram A n) →
        family-dependent-sequential-diagram A B n x)
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
    family-dependent-sequential-diagram A B n x
  map-section-dependent-sequential-diagram = pr1 s

  naturality-map-section-dependent-sequential-diagram :
    naturality-section-dependent-sequential-diagram A B
      map-section-dependent-sequential-diagram
  naturality-map-section-dependent-sequential-diagram = pr2 s
```

## References

1. Kristina Sojakova, Floris van Doorn, and Egbert Rijke. 2020. Sequential
   Colimits in Homotopy Type Theory. In Proceedings of the 35th Annual ACM/IEEE
   Symposium on Logic in Computer Science (LICS '20). Association for Computing
   Machinery, New York, NY, USA, 845–858,
   [DOI:10.1145](https://doi.org/10.1145/3373718.3394801)
