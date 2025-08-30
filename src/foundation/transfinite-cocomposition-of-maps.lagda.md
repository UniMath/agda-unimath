# Transfinite cocomposition of maps

```agda
module foundation.transfinite-cocomposition-of-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.inverse-sequential-diagrams
open import foundation.sequential-limits
open import foundation.universe-levels
```

</details>

## Idea

Given an
[inverse sequential diagram of types](foundation.inverse-sequential-diagrams.md),
i.e. a certain infinite [sequence](lists.dependent-sequences.md) of maps `fₙ`:

```text
      ⋯        fₙ      ⋯      f₁      f₀
  ⋯ ---> Aₙ₊₁ ---> Aₙ ---> ⋯ ---> A₁ ---> A₀,
```

we can form the **transfinite cocomposition** of `f` by taking the canonical map
from the [standard sequential limit](foundation.sequential-limits.md) `limₙ Aₙ`
into `A₀`.

## Definitions

### The transfinite cocomposition of an inverse sequential diagram of maps

```agda
module _
  {l : Level} (f : inverse-sequential-diagram l)
  where

  transfinite-cocomp :
    standard-sequential-limit f → family-inverse-sequential-diagram f 0
  transfinite-cocomp x = sequence-standard-sequential-limit f x 0
```

## Table of files about sequential limits

The following table lists files that are about sequential limits as a general
concept.

{{#include tables/sequential-limits.md}}
