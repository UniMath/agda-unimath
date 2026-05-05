# Sequentially compact types

```agda
module synthetic-homotopy-theory.sequentially-compact-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-products-propositions
open import foundation.propositions
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-sequential-diagrams
open import synthetic-homotopy-theory.sequential-diagrams
open import synthetic-homotopy-theory.universal-property-sequential-colimits
```

</details>

## Idea

A **sequentially compact type** is a type `X` such that exponentiating by `X`
commutes with
[sequential colimits](synthetic-homotopy-theory.universal-property-sequential-colimits.md)

```text
  colimₙ (X → Aₙ) ≃ (X → colimₙ Aₙ)
```

for every [cotower](synthetic-homotopy-theory.sequential-diagrams.md) `Aₙ`.

## Definitions

### The predicate of being a sequentially compact type

```agda
module _
  {l1 : Level} (X : UU l1)
  where

  is-sequentially-compact : UUω
  is-sequentially-compact =
    {l2 l3 : Level} (A : sequential-diagram l2) {A∞ : UU l3}
    (c : cocone-sequential-diagram A A∞) →
    universal-property-sequential-colimit c →
    universal-property-sequential-colimit
      ( cocone-postcomp-sequential-diagram X A c)
```

## References

{{#bibliography}} {{#reference Rij19}}
