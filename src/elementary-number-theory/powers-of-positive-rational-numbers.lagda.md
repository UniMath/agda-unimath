# Powers of positive rational numbers

```agda
module elementary-number-theory.powers-of-positive-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.multiplication-positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.bernoullis-inequality-positive-rational-numbers
open import elementary-number-theory.multiplicative-group-of-positive-rational-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import group-theory.powers-of-elements-groups
```

</details>

## Idea

The
{{#concept "power operation" Disambiguation="raising a rational number to a natural number power" Agda=power-ℚ}}
on the [positive](elementary-number-theory.positive-rational-numbers.md)
[rational numbers](elementary-number-theory.rational-numbers.md) `n x ↦ xⁿ`,
which is defined by [iteratively](foundation.iterating-functions.md) multiplying
`x` with itself `n` times.

## Definition

```agda
power-ℚ⁺ : ℕ → ℚ⁺ → ℚ⁺
power-ℚ⁺ = power-Group group-mul-ℚ⁺
```

## Properties

### For any positive rational `ε`, `(1 + ε)ⁿ` grows without bound

```agda

```

## See also

- [Powers of elements of a group](group-theory.powers-of-elements-groups.md)
