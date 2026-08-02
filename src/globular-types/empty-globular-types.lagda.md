# Empty globular types

```agda
{-# OPTIONS --guardedness #-}

module globular-types.empty-globular-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.empty-types
open import foundation.universe-levels

open import globular-types.constant-globular-types
open import globular-types.globular-types
```

</details>

## Idea

A [globular type](globular-types.globular-types.md) is said to be
{{#concept "empty" Disambiguation="globular type"}} if its type of 0-cells is
[empty](foundation.empty-types.md).

The {{#concept "standard empty globular type" Agda=empty-Globular-Type}} is
defined to be the
[constant globular type](globular-types.constant-globular-types.md) at the empty
type. That is, the standard empty globular type is the globular type `𝟎` given
by

```text
  𝟎₀ := ∅
  𝟎' x y := 𝟎.
```

## Definitions

### The predicate of being an empty globular type

```agda
module _
  {l1 l2 : Level} (G : Globular-Type l1 l2)
  where

  is-empty-Globular-Type : UU l1
  is-empty-Globular-Type = is-empty (0-cell-Globular-Type G)
```

### The standard empty globular type

```agda
empty-Globular-Type : Globular-Type lzero lzero
empty-Globular-Type = constant-Globular-Type empty
```

### The empty globular type of an arbitrary universe level

```agda
raise-empty-Globular-Type : (l1 l2 : Level) → Globular-Type l1 l2
0-cell-Globular-Type (raise-empty-Globular-Type l1 l2) =
  raise-empty l1
1-cell-globular-type-Globular-Type (raise-empty-Globular-Type l1 l2) x y =
  raise-empty-Globular-Type l2 l2
```
