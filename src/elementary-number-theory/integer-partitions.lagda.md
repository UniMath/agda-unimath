#  Integer partitions

```agda
module elementary-number-theory.integer-partitions where

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonzero-natural-numbers

open import foundation.dependent-pair-types
open import foundation.fibers-of-maps
open import foundation.identity-types
open import foundation.universe-levels

open import univalent-combinatorics.finite-types
open import univalent-combinatorics.lists
```

## Idea

An integer partition of a natural number n is a list of nonzero natural numbers that sum up to n, up to reordering. We define the number `p n` of integer partitions of `n` as the number of connected components in the type of finite Ferrer diagrams of `Fin n`.
