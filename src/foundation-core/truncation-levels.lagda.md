# Truncation levels

```agda
{-# OPTIONS --safe #-}
```

<details><summary>Imports</summary>
```agda
module foundation-core.truncation-levels where
open import foundation-core.universe-levels
```
</details>

## Idea

The type of truncation levels is a type similar to the type of natural numbers, but starting the count at -2, so that sets have truncation level 0.

## Definition

```agda
data 𝕋 : UU lzero where
  neg-two-𝕋 : 𝕋
  succ-𝕋 : 𝕋 → 𝕋

neg-one-𝕋 : 𝕋
neg-one-𝕋 = succ-𝕋 neg-two-𝕋

zero-𝕋 : 𝕋
zero-𝕋 = succ-𝕋 neg-one-𝕋

one-𝕋 : 𝕋
one-𝕋 = succ-𝕋 zero-𝕋

two-𝕋 : 𝕋
two-𝕋 = succ-𝕋 one-𝕋
```
