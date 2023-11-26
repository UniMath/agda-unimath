# Compact types

```agda
module orthogonal-factorization-systems.compact-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositions
open import foundation.universe-levels

open import orthogonal-factorization-systems.factorization-operations-function-classes
open import orthogonal-factorization-systems.factorizations-of-maps-global-function-classes
open import orthogonal-factorization-systems.global-function-classes

open import synthetic-homotopy-theory.cocones-under-sequential-diagrams
open import synthetic-homotopy-theory.sequential-diagrams
open import synthetic-homotopy-theory.universal-property-sequential-colimits
```

</details>

## Idea

A **(sequentially) compact type** is a type `X` such that exponentiating with
`X` commutes with
[sequential colimits](synthetic-homotopy-theory.universal-property-sequential-colimits.md)
for every [cotower](synthetic-homotopy-theory.sequential-diagrams.md) `Aₙ`:

```text
  (colimₙ (X → Aₙ)) ≃ (X → colimₙ Aₙ.)
```

## Definitions

### The predicate of being a compact type

```agda
module _
  {l1 : Level} (X : UU l1)
  where

  is-compact : UUω
  is-compact =
    {l2 l3 : Level} (A : sequential-diagram l2) {A∞ : UU l3}
    (c : cocone-sequential-diagram A A∞) →
    ((l : Level) → universal-property-sequential-colimit l A c) →
    (l : Level) →
    universal-property-sequential-colimit l
      ( postcomp-sequential-diagram X A)
      ( cocone-postcomp-sequential-diagram X A c)
```

## References

- <a name="classifying-types"></a>Egbert Rijke, _Classifying Types_
  ([arXiv:1906.09435](https://arxiv.org/abs/1906.09435))
