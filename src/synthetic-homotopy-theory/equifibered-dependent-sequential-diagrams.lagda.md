# Equifibered dependent sequential diagrams

```agda
module synthetic-homotopy-theory.equifibered-dependent-sequential-diagrams where
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
{{#concept "equifibered dependent sequential diagram" Disambiguation="over a sequential diagram" Agda=equifibered-dependent-sequential-diagram}}
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

### Equifibered dependent sequential diagrams

```agda
module _
  {l1 : Level} (A : sequential-diagram l1)
  where

  equifibered-dependent-sequential-diagram : (l : Level) → UU (l1 ⊔ lsuc l)
  equifibered-dependent-sequential-diagram l =
    Σ ( (n : ℕ) → family-sequential-diagram A n → UU l)
      ( λ B →
        (n : ℕ) (a : family-sequential-diagram A n) →
        B n a ≃ B (succ-ℕ n) (map-sequential-diagram A n a))
```

### Components of an equifibered dependent sequential diagram

```agda
module _
  {l1 l2 : Level} {A : sequential-diagram l1}
  (B : equifibered-dependent-sequential-diagram A l2)
  where

  family-equifibered-dependent-sequential-diagram :
    (n : ℕ) → family-sequential-diagram A n → UU l2
  family-equifibered-dependent-sequential-diagram = pr1 B

  equiv-equifibered-dependent-sequential-diagram :
    (n : ℕ) (a : family-sequential-diagram A n) →
    family-equifibered-dependent-sequential-diagram n a ≃
    family-equifibered-dependent-sequential-diagram
      ( succ-ℕ n)
      ( map-sequential-diagram A n a)
  equiv-equifibered-dependent-sequential-diagram = pr2 B

  map-equifibered-dependent-sequential-diagram :
    (n : ℕ) (a : family-sequential-diagram A n) →
    family-equifibered-dependent-sequential-diagram n a →
    family-equifibered-dependent-sequential-diagram
      ( succ-ℕ n)
      ( map-sequential-diagram A n a)
  map-equifibered-dependent-sequential-diagram n a =
    map-equiv (equiv-equifibered-dependent-sequential-diagram n a)

  is-equiv-map-equifibered-dependent-sequential-diagram :
    (n : ℕ) (a : family-sequential-diagram A n) →
    is-equiv (map-equifibered-dependent-sequential-diagram n a)
  is-equiv-map-equifibered-dependent-sequential-diagram n a =
    is-equiv-map-equiv (equiv-equifibered-dependent-sequential-diagram n a)

  dependent-sequential-diagram-equifibered-dependent-sequential-diagram :
    dependent-sequential-diagram A l2
  pr1 dependent-sequential-diagram-equifibered-dependent-sequential-diagram =
    family-equifibered-dependent-sequential-diagram
  pr2 dependent-sequential-diagram-equifibered-dependent-sequential-diagram =
    map-equifibered-dependent-sequential-diagram
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

  is-equifibered-dependent-sequential-diagram-equifibered-dependent-sequential-diagram :
    (B : equifibered-dependent-sequential-diagram A l2) →
    is-equifibered-dependent-sequential-diagram
      ( dependent-sequential-diagram-equifibered-dependent-sequential-diagram B)
  is-equifibered-dependent-sequential-diagram-equifibered-dependent-sequential-diagram
    B =
    is-equiv-map-equifibered-dependent-sequential-diagram B
```

## Properties

### Dependent sequential diagrams which are equifibered are equifibered dependent sequential diagrams

To construct an equifibered dependent sequential diagram over `A`, it suffices
to construct a dependent sequential diagram `(B, b)` over `A`, and show that the
maps `bₙ` are equivalences.

```agda
module _
  {l1 l2 : Level} {A : sequential-diagram l1}
  (B : dependent-sequential-diagram A l2)
  where

  equifibered-dependent-sequential-diagram-dependent-sequential-diagram :
    is-equifibered-dependent-sequential-diagram B →
    equifibered-dependent-sequential-diagram A l2
  pr1
    ( equifibered-dependent-sequential-diagram-dependent-sequential-diagram _) =
    family-dependent-sequential-diagram B
  pr2
    ( equifibered-dependent-sequential-diagram-dependent-sequential-diagram
      is-equiv-map)
    n a =
    ( map-dependent-sequential-diagram B n a , is-equiv-map n a)
```

## References

{{#bibliography}}
