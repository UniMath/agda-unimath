# Terminal globular types

```agda
{-# OPTIONS --guardedness #-}

open import foundation.function-extensionality-axiom

module
  globular-types.terminal-globular-types
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types funext
open import foundation.universe-levels

open import globular-types.globular-maps funext
open import globular-types.globular-types
```

</details>

## Idea

A [globular type](globular-types.globular-types.md) `G` is said to be
{{#concept "terminal" Disambiguation="globular type" Agda=is-terminal-Globular-Type}}
if for any globular type `H` the type of
[globular maps](globular-types.globular-maps.md) `H → G` is
[contractible](foundation-core.contractible-types.md).

## Definitions

### The predicate of being a terminal globular type

```agda
is-terminal-Globular-Type :
  {l1 l2 : Level} → Globular-Type l1 l2 → UUω
is-terminal-Globular-Type G =
  {l3 l4 : Level} (H : Globular-Type l3 l4) → is-contr (globular-map H G)
```
