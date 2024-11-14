# Terminal globular types

```agda
{-# OPTIONS --guardedness #-}

module structured-types.terminal-globular-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.universe-levels

open import structured-types.globular-maps
open import structured-types.globular-types
```

</details>

## Idea

A [globular type](structured-types.globular-types.md) `G` is said to be
{{#concept "terminal" Disambiguation="globular type" Agda=is-terminal-Globular-Type}}
if for any globular type `H` the type of
[globular maps](structured-types.globular-maps.md) `H → G` is
[contractible](foundation-core.contractible-types.md).

## Definitions

### The predicate of being a terminal globular type

```agda
is-terminal-Globular-Type :
  {l1 l2 : Level} → Globular-Type l1 l2 → UUω
is-terminal-Globular-Type G =
  {l3 l4 : Level} (H : Globular-Type l3 l4) → is-contr (globular-map H G)
```
