# Equifibered sequential diagrams

```agda
module synthetic-homotopy-theory.equifibered-sequential-diagrams where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.universe-levels

open import synthetic-homotopy-theory.dependent-sequential-diagrams
open import synthetic-homotopy-theory.sequential-diagrams
```

</details>

## Idea

An
{{#concept "equifibered sequential diagram" Disambiguation="over a sequential diagram" Agda=equifibered-sequential-diagram}}
over a [sequential diagram](synthetic-homotopy-theory.sequential-diagrams.md)
`(A, a)` consists of a type family `B : (n : ℕ) → Aₙ → 𝒰`
[equipped](foundation.structure.md) with a family of fiberwise equivalences

```text
bₙ : (a : Aₙ) → Bₙ a ≃ Bₙ₊₁ (aₙ a) .
```

The term "equifibered" comes from the equivalent definition as
[dependent sequential diagrams](synthetic-homotopy-theory.dependent-sequential-diagrams.md)
over `(A, a)`

```text
     b₀      b₁      b₂
 B₀ ---> B₁ ---> B₂ ---> ⋯
 |       |       |
 |       |       |
 ↡       ↡       ↡
 A₀ ---> A₁ ---> A₂ ---> ⋯ ,
     a₀      a₁      a₂
```

which are said to be "fibered over `A`", whose maps `bₙ` are equivalences. This
terminology was originally introduced by Charles Rezk in _Toposes and Homotopy
Toposes_ {{#cite Rezk10HomotopyToposes}}.

## Definitions

### Equifibered sequential diagrams

```agda
module _
  {l1 : Level} (A : sequential-diagram l1)
  where

  equifibered-sequential-diagram : (l : Level) → UU (l1 ⊔ lsuc l)
  equifibered-sequential-diagram l =
    Σ ( (n : ℕ) → family-sequential-diagram A n → UU l)
      ( λ B →
        (n : ℕ) (a : family-sequential-diagram A n) →
        B n a ≃ B (succ-ℕ n) (map-sequential-diagram A n a))
```

### Components of an equifibered sequential diagram

```agda
module _
  {l1 l2 : Level} {A : sequential-diagram l1}
  (B : equifibered-sequential-diagram A l2)
  where

  family-equifibered-sequential-diagram :
    (n : ℕ) → family-sequential-diagram A n → UU l2
  family-equifibered-sequential-diagram = pr1 B

  equiv-equifibered-sequential-diagram :
    (n : ℕ) (a : family-sequential-diagram A n) →
    family-equifibered-sequential-diagram n a ≃
    family-equifibered-sequential-diagram
      ( succ-ℕ n)
      ( map-sequential-diagram A n a)
  equiv-equifibered-sequential-diagram = pr2 B

  map-equifibered-sequential-diagram :
    (n : ℕ) (a : family-sequential-diagram A n) →
    family-equifibered-sequential-diagram n a →
    family-equifibered-sequential-diagram
      ( succ-ℕ n)
      ( map-sequential-diagram A n a)
  map-equifibered-sequential-diagram n a =
    map-equiv (equiv-equifibered-sequential-diagram n a)

  is-equiv-map-equifibered-sequential-diagram :
    (n : ℕ) (a : family-sequential-diagram A n) →
    is-equiv (map-equifibered-sequential-diagram n a)
  is-equiv-map-equifibered-sequential-diagram n a =
    is-equiv-map-equiv (equiv-equifibered-sequential-diagram n a)

  dependent-sequential-diagram-equifibered-sequential-diagram :
    dependent-sequential-diagram A l2
  pr1 dependent-sequential-diagram-equifibered-sequential-diagram =
    family-equifibered-sequential-diagram
  pr2 dependent-sequential-diagram-equifibered-sequential-diagram =
    map-equifibered-sequential-diagram
```

### The predicate on dependent sequential diagrams of being equifibered

```agda
module _
  {l1 l2 : Level} {A : sequential-diagram l1}
  where

  is-equifibered-dependent-sequential-diagram :
    (B : dependent-sequential-diagram A l2) → UU (l1 ⊔ l2)
  is-equifibered-dependent-sequential-diagram B =
    (n : ℕ) (a : family-sequential-diagram A n) →
    is-equiv (map-dependent-sequential-diagram B n a)

  is-equifibered-dependent-sequential-diagram-equifibered-sequential-diagram :
    (B : equifibered-sequential-diagram A l2) →
    is-equifibered-dependent-sequential-diagram
      ( dependent-sequential-diagram-equifibered-sequential-diagram B)
  is-equifibered-dependent-sequential-diagram-equifibered-sequential-diagram
    B =
    is-equiv-map-equifibered-sequential-diagram B
```

## Properties

### Dependent sequential diagrams which are equifibered are equifibered sequential diagrams

To construct an equifibered sequential diagram over `A`, it suffices to
construct a dependent sequential diagram `(B, b)` over `A`, and show that the
maps `bₙ` are equivalences.

```agda
module _
  {l1 l2 : Level} {A : sequential-diagram l1}
  (B : dependent-sequential-diagram A l2)
  where

  equifibered-sequential-diagram-dependent-sequential-diagram :
    is-equifibered-dependent-sequential-diagram B →
    equifibered-sequential-diagram A l2
  pr1
    ( equifibered-sequential-diagram-dependent-sequential-diagram _) =
    family-dependent-sequential-diagram B
  pr2
    ( equifibered-sequential-diagram-dependent-sequential-diagram
      is-equiv-map)
    n a =
    ( map-dependent-sequential-diagram B n a , is-equiv-map n a)
```

## References

{{#bibliography}}
