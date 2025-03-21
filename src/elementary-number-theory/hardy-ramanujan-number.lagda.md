# The Hardy-Ramanujan number

```agda
module elementary-number-theory.hardy-ramanujan-number where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.taxicab-numbers

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.unit-type
```

</details>

## Idea

The
{{#concept "Hardy-Ramanujan number" Agda=Hardy-Ramanujan-ℕ WD="1729" WDID=Q825176 Agda=Hardy-Ramanujan-ℕ}}
is the number `1729`. This number is the second
[taxicab number](elementary-number-theory.taxicab-numbers.md), i.e., it is the
least natural number that can be written as a sum of cubes of positive natural
numbers in exactly two distinct ways. Specifically, we have the identifications

```text
  1³ + 12³ ＝ 1729    and    9³ + 10³ ＝ 1729.
```

## Definition

### The Hardy-Ramanujan number

```agda
Hardy-Ramanujan-ℕ : ℕ
Hardy-Ramanujan-ℕ = 1729
```

## Properties

### Two decompositions of the Hardy-Ramanujan number into sums of cubes of two positive natural numbers

```agda
first-sum-of-cubes-decomposition-Hardy-Ramanujan-ℕ :
  sum-of-cubes-decomposition-ℕ Hardy-Ramanujan-ℕ
pr1 first-sum-of-cubes-decomposition-Hardy-Ramanujan-ℕ =
  (1 , is-nonzero-one-ℕ)
pr1 (pr2 first-sum-of-cubes-decomposition-Hardy-Ramanujan-ℕ) =
  (12 , is-nonzero-succ-ℕ 11)
pr1 (pr2 (pr2 first-sum-of-cubes-decomposition-Hardy-Ramanujan-ℕ)) =
  star
pr2 (pr2 (pr2 first-sum-of-cubes-decomposition-Hardy-Ramanujan-ℕ)) =
  refl

second-sum-of-cubes-decomposition-Hardy-Ramanujan-ℕ :
  sum-of-cubes-decomposition-ℕ Hardy-Ramanujan-ℕ
pr1 second-sum-of-cubes-decomposition-Hardy-Ramanujan-ℕ =
  (9 , is-nonzero-succ-ℕ 8)
pr1 (pr2 second-sum-of-cubes-decomposition-Hardy-Ramanujan-ℕ) =
  (10 , is-nonzero-succ-ℕ 9)
pr1 (pr2 (pr2 second-sum-of-cubes-decomposition-Hardy-Ramanujan-ℕ)) =
  star
pr2 (pr2 (pr2 second-sum-of-cubes-decomposition-Hardy-Ramanujan-ℕ)) =
  refl
```

## External links

- [1729 (number)](<https://en.wikipedia.org/wiki/1729_(number)>) at Wikipedia
