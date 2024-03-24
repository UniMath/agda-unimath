# Impredicative universes

```agda
module foundation.impredicative-universes where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import foundation-core.propositions
open import foundation-core.small-types
```

</details>

## Idea

A universe `𝒰` is {{#concept "impredicative"}} if the type of
[propositions](foundation-core.propositions.md) in `𝒰` is `𝒰`-small.

## Definition

```agda
is-impredicative-UU : (l : Level) → UU (lsuc l)
is-impredicative-UU l = is-small l (Prop l)
```

## See also

- [Impredicative encodings of the logical operations](foundation.impredicative-encodings.md)
