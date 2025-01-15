# Farey fractions

```agda
module elementary-number-theory.farey-fractions where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.integer-fractions

open import foundation.universe-levels
```

</details>

## Idea

A {{#concept "Farey fraction" Agda=farey-fraction}} is a [reduced](elementary-number-theory.reduced-integer-fractions.md) [integer fraction](elementary-number-theory.integer-fractions.md) between $0$ and $1$ inclusive. More specifically, a Farey fraction of order $n$ is a reduced integer fraction between $0$ and $1$ whose denominator does not exceed $n$.

The Farey fractions ℱ can be inductively generated mutually with a binary relation $R$ with the following constructors:

```text
  0 : ℱ
  1 : ℱ
  𝓂 : (x y : ℱ) → ℛ x y → ℱ

  𝓈 : ℛ 0 1
  𝓇 : (x y : ℱ) (r : ℛ x y) → ℛ x (𝓂 x y r)
  𝓁 : (x y : ℱ) (r : ℛ x y) → ℛ (𝓂 x y r) y
```

The operation $m$ returns the {{#concept "mediant" Disambiguation="Farey fractions"}} of two adjacent Farey fractions.

Farey fractions appear in Chapter 3 of {{#cite HW08}}, but they are covered in more detail in Chapter 6 of {{#cite NZM}}. 

## Definitions

### The inductively generated Farey fractions

```agda
mutual

  data
    farey-fraction : UU lzero
    where

    zero-farey-fraction : farey-fraction
    one-farey-fraction : farey-fraction

    mediant-farey-fraction :
      (x y : farey-fraction) → adjacent-farey-fraction x y → farey-fraction

  data
    adjacent-farey-fraction : farey-fraction → farey-fraction → UU lzero
    where

    adjacent-zero-one-farey-fraction :
      adjacent-farey-fraction zero-farey-fraction one-farey-fraction

    right-adjacent-mediant-farey-fraction :
      (x y : farey-fraction) (H : adjacent-farey-fraction x y) →
      adjacent-farey-fraction x (mediant-farey-fraction x y H)

    left-adjacent-mediant-farey-fraction :
      (x y : farey-fraction) (H : adjacent-farey-fraction x y) →
      adjacent-farey-fraction (mediant-farey-fraction x y H) y
```

### The inclusion of Farey fractions into the integer fractions

```agda
integer-fraction-farey-fraction :
  farey-fraction → fraction-ℤ
integer-fraction-farey-fraction = ?
```

## References

{{#bibliography}}
