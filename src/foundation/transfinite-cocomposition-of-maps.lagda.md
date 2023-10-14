# Transfinite cocomposition of maps

```agda
module foundation.transfinite-cocomposition-of-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.limits-towers
open import foundation.towers
open import foundation.universe-levels
```

</details>

## Idea

Given an infinite [sequence](foundation.dependent-sequences.md) of maps, i.e. a
[tower](foundation.towers.md) `fₙ`:

```text
      ⋯         fₙ       ⋯       f₁       f₀
  ⋯ ----> Aₙ₊₁ ----> Aₙ ----> ⋯ ----> A₁ ----> A₀,
```

we can form the **transfinite cocomposition** of `fₙ` by taking the canonical
map from the [standard limit of the tower](foundation.limits-towers.md) into
`A₀`.

## Definitions

### The transfinite composition of a tower of maps

```agda
module _
  {l : Level} (f : Tower l)
  where

  transfinite-cocomp : standard-limit-Tower f → type-Tower f 0
  transfinite-cocomp x = sequence-standard-limit-Tower f x 0
```
