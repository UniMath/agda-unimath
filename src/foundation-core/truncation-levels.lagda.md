# Truncation levels

```agda
module foundation-core.truncation-levels where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels
```

</details>

## Idea

The type of **truncation levels** is a type similar to the type of
[natural numbers](elementary-number-theory.natural-numbers.md), but starting the
count at -2, so that [sets](foundation-core.sets.md) have
[truncation](foundation-core.truncated-types.md) level 0.

## Definitions

### The type of truncation levels

```agda
data 𝕋 : UU lzero where
  neg-two-𝕋 : 𝕋
  succ-𝕋 : 𝕋 → 𝕋
```

### Aliases for common truncation levels

```agda
neg-one-𝕋 : 𝕋
neg-one-𝕋 = succ-𝕋 neg-two-𝕋

zero-𝕋 : 𝕋
zero-𝕋 = succ-𝕋 neg-one-𝕋

one-𝕋 : 𝕋
one-𝕋 = succ-𝕋 zero-𝕋

two-𝕋 : 𝕋
two-𝕋 = succ-𝕋 one-𝕋
```
