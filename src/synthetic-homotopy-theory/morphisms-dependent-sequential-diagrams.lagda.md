# Morphisms of dependent sequential diagrams

```agda
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module synthetic-homotopy-theory.morphisms-dependent-sequential-diagrams
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.commuting-squares-of-maps funext univalence
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import synthetic-homotopy-theory.dependent-sequential-diagrams funext univalence
open import synthetic-homotopy-theory.sequential-diagrams funext univalence
```

</details>

## Idea

Consider two
[dependent sequential diagrams](synthetic-homotopy-theory.dependent-sequential-diagrams.md)

```text
     b₀      b₁      b₂            c₀      c₁      c₂
 B₀ ---> B₁ ---> B₂ ---> ⋯     C₀ ---> C₁ ---> C₂ ---> ⋯
 |       |       |             |       |       |
 |       |       |             |       |       |
 ↡       ↡       ↡             ↡       ↡       ↡
 A₀ ---> A₁ ---> A₂ ---> ⋯     A₀ ---> A₁ ---> A₂ ---> ⋯ .
     a₀      a₁      a₂            a₀      a₁      a₂
```

A
{{#concept "morphism of dependent sequential diagrams" Agda=hom-dependent-sequential-diagram}}
between them is a family of fiberwise maps

```text
hₙ : (a : Aₙ) → Bₙ a → Cₙ a
```

[equipped](foundation.structure.md) with a family of fiberwise
[homotopies](foundation-core.homotopies.md) making the squares

```text
                 hₙ a
     Bₙ a -----------------> Cₙ a
       |                       |
  bₙ a |                       | cₙ a
       |                       |
       ∨                       ∨
  Bₙ₊₁ (aₙ a) ----------> Cₙ₊₁ (aₙ a)
              hₙ₊₁ (aₙ a)
```

[commute](foundation-core.commuting-squares-of-maps.md).

## Definitions

### Morphisms of dependent sequential diagrams

```agda
module _
  {l1 l2 l3 : Level} {A : sequential-diagram l1}
  (B : dependent-sequential-diagram A l2)
  (C : dependent-sequential-diagram A l3)
  where

  coherence-hom-dependent-sequential-diagram :
    ( (n : ℕ) (a : family-sequential-diagram A n) →
      family-dependent-sequential-diagram B n a →
      family-dependent-sequential-diagram C n a) →
    UU (l1 ⊔ l2 ⊔ l3)
  coherence-hom-dependent-sequential-diagram h =
    (n : ℕ) (a : family-sequential-diagram A n) →
    coherence-square-maps
      ( h n a)
      ( map-dependent-sequential-diagram B n a)
      ( map-dependent-sequential-diagram C n a)
      ( h (succ-ℕ n) (map-sequential-diagram A n a))

  hom-dependent-sequential-diagram : UU (l1 ⊔ l2 ⊔ l3)
  hom-dependent-sequential-diagram =
    Σ ( (n : ℕ) (a : family-sequential-diagram A n) →
        family-dependent-sequential-diagram B n a →
        family-dependent-sequential-diagram C n a)
      ( coherence-hom-dependent-sequential-diagram)
```

### Components of a morphism of sequential diagrams

```agda
module _
  {l1 l2 l3 : Level} {A : sequential-diagram l1}
  {B : dependent-sequential-diagram A l2}
  (C : dependent-sequential-diagram A l3)
  (h : hom-dependent-sequential-diagram B C)
  where

  map-hom-dependent-sequential-diagram :
    (n : ℕ) (a : family-sequential-diagram A n) →
    family-dependent-sequential-diagram B n a →
    family-dependent-sequential-diagram C n a
  map-hom-dependent-sequential-diagram = pr1 h

  coh-hom-dependent-sequential-diagram :
    coherence-hom-dependent-sequential-diagram B C
      ( map-hom-dependent-sequential-diagram)
  coh-hom-dependent-sequential-diagram = pr2 h
```
