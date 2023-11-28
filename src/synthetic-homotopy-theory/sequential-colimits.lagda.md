# Sequential colimits

```agda
module synthetic-homotopy-theory.sequential-colimits where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.commuting-squares-of-homotopies
open import foundation.commuting-triangles-of-maps
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.homotopies
open import foundation.universe-levels
open import foundation.whiskering-homotopies

open import synthetic-homotopy-theory.cocones-under-sequential-diagrams
open import synthetic-homotopy-theory.coequalizers
open import synthetic-homotopy-theory.dependent-universal-property-sequential-colimits
open import synthetic-homotopy-theory.sequential-diagrams
open import synthetic-homotopy-theory.universal-property-sequential-colimits
```

</details>

## Idea

Given a [sequential diagram](synthetic-homotopy-theory.sequential-diagrams.md)
`(A, a)`, we can construct its **standard sequential colimit**, which is a
[cocone under it](synthetic-homotopy-theory.cocones-under-sequential-diagrams.md)
satisfying the
[universal property of sequential colimits](synthetic-homotopy-theory.universal-property-sequential-colimits.md).

In other words, the sequential colimit `A∞` universally completes the diagram

```text
     a₀      a₁      a₂
 A₀ ---> A₁ ---> A₂ ---> ⋯ ---> A∞
```

## Properties

### All sequential diagrams admit a standard colimit

The standard colimit may be constructed from
[coequalizers](synthetic-homotopy-theory.coequalizers.md), because we
[have shown](synthetic-homotopy-theory.universal-property-sequential-colimits.md)
that cocones of sequential diagrams correspond to a certain class of
[coforks](synthetic-homotopy-theory.coforks.md), and the coequalizers correspond
to sequential colimits. Since all coequalizers exist, we conclude that all
sequential colimits exist.

```agda
module _
  { l : Level} (A : sequential-diagram l)
  where

  abstract
    standard-sequential-colimit : UU l
    standard-sequential-colimit =
      canonical-coequalizer
        ( bottom-map-cofork-cocone-sequential-diagram A)
        ( top-map-cofork-cocone-sequential-diagram A)

    cocone-standard-sequential-colimit :
      cocone-sequential-diagram A standard-sequential-colimit
    cocone-standard-sequential-colimit =
      cocone-sequential-diagram-cofork A
        ( cofork-canonical-coequalizer
          ( bottom-map-cofork-cocone-sequential-diagram A)
          ( top-map-cofork-cocone-sequential-diagram A))

    dup-standard-sequential-colimit :
      dependent-universal-property-sequential-colimit A
        ( cocone-standard-sequential-colimit)
    dup-standard-sequential-colimit =
      dependent-universal-property-sequential-colimit-dependent-universal-property-coequalizer
        ( A)
        ( cocone-standard-sequential-colimit)
        ( dup-canonical-coequalizer
          ( bottom-map-cofork-cocone-sequential-diagram A)
          ( top-map-cofork-cocone-sequential-diagram A))

    up-standard-sequential-colimit :
      universal-property-sequential-colimit A cocone-standard-sequential-colimit
    up-standard-sequential-colimit =
      universal-property-dependent-universal-property-sequential-colimit A
        ( cocone-standard-sequential-colimit)
        ( dup-standard-sequential-colimit)

  map-cocone-standard-sequential-colimit :
    ( n : ℕ) → family-sequential-diagram A n → standard-sequential-colimit
  map-cocone-standard-sequential-colimit =
    map-cocone-sequential-diagram A cocone-standard-sequential-colimit

  coherence-triangle-cocone-standard-sequential-colimit :
    ( n : ℕ) →
    coherence-triangle-maps
      ( map-cocone-standard-sequential-colimit n)
      ( map-cocone-standard-sequential-colimit (succ-ℕ n))
      ( map-sequential-diagram A n)
  coherence-triangle-cocone-standard-sequential-colimit =
    coherence-triangle-cocone-sequential-diagram A
      ( cocone-standard-sequential-colimit)
```

### Homotopies between maps from the standard sequential colimit

```agda
module _
  { l1 l2 : Level} (A : sequential-diagram l1) {X : UU l2}
  ( f g : standard-sequential-colimit A → X)
  where

  htpy-standard-sequential-colimit : UU (l1 ⊔ l2)
  htpy-standard-sequential-colimit =
    Σ ( ( n : ℕ) →
        f ∘ map-cocone-standard-sequential-colimit A n ~
        g ∘ map-cocone-standard-sequential-colimit A n)
      ( λ h →
        ( n : ℕ) →
        coherence-square-homotopies
          ( h n)
          ( f ·l coherence-triangle-cocone-standard-sequential-colimit A n)
          ( g ·l coherence-triangle-cocone-standard-sequential-colimit A n)
          ( h (succ-ℕ n) ·r map-sequential-diagram A n))
```
