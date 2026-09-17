# Sequences in rings

```agda
module ring-theory.sequences-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-products-propositions
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.semigroups

open import lists.sequences

open import ring-theory.commuting-elements-rings
open import ring-theory.function-rings
open import ring-theory.rings
```

</details>

## Idea

The type of [sequences](lists.sequences.md) in a [ring](ring-theory.rings.md)
inherits the [function](ring-theory.function-rings.md) ring structure with
pointwise addition and multiplication. This is the
{{#concept "ring of sequences in a ring" Agda=sequence-Ring}}.

## Definition

### The ring of sequences in a ring with pointwise operations

```agda
module _
  {l : Level} (R : Ring l)
  where

  sequence-Ring : Ring l
  sequence-Ring = function-Ring R ℕ

  type-sequence-Ring : UU l
  type-sequence-Ring = type-Ring sequence-Ring

  ab-sequence-Ring : Ab l
  ab-sequence-Ring = ab-Ring sequence-Ring

  zero-sequence-Ring : type-sequence-Ring
  zero-sequence-Ring = zero-Ring sequence-Ring

  add-sequence-Ring :
    type-sequence-Ring → type-sequence-Ring → type-sequence-Ring
  add-sequence-Ring =
    add-Ring sequence-Ring
```
