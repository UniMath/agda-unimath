# Sequences in semirings

```agda
module ring-theory.sequences-semirings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-products-propositions
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import group-theory.commutative-monoids
open import group-theory.commuting-elements-monoids
open import group-theory.semigroups

open import lists.sequences

open import ring-theory.function-semirings
open import ring-theory.semirings
```

</details>

## Idea

The type of [sequences](lists.sequences.md) in a
[semiring](ring-theory.semirings.md) inherits the
[function](ring-theory.function-semirings.md) semiring structure with pointwise
addition and multiplication. This is the
{{#concept "semiring of sequences in a semiring" Agda=sequence-Semiring}}.

## Definition

### The semiring of sequences in a semiring with pointwise operations

```agda
module _
  {l : Level} (R : Semiring l)
  where

  sequence-Semiring : Semiring l
  sequence-Semiring = function-Semiring R ℕ

  type-sequence-Semiring : UU l
  type-sequence-Semiring = type-Semiring sequence-Semiring

  additive-commutative-monoid-sequence-Semiring : Commutative-Monoid l
  additive-commutative-monoid-sequence-Semiring =
    additive-commutative-monoid-Semiring sequence-Semiring

  zero-sequence-Semiring : type-sequence-Semiring
  zero-sequence-Semiring = zero-Semiring sequence-Semiring

  add-sequence-Semiring :
    type-sequence-Semiring → type-sequence-Semiring → type-sequence-Semiring
  add-sequence-Semiring =
    add-Semiring sequence-Semiring
```
