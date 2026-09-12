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

## Properties

### Totally commuting sequences in a ring

Two sequences `a`, `b` are called **totally commuting** if `aᵢbⱼ ＝ bⱼaᵢ` for
all `i j : ℕ`.

```agda
module _
  {l : Level} (R : Ring l) (a b : type-sequence-Ring R)
  where

  all-commute-prop-sequence-Ring : Prop l
  all-commute-prop-sequence-Ring =
    Π-Prop ℕ (λ i → Π-Prop ℕ (λ j → commute-prop-Ring R (a i) (b j)))

  all-commute-sequence-Ring : UU l
  all-commute-sequence-Ring = type-Prop all-commute-prop-sequence-Ring

  is-prop-all-commute-sequence-Ring : is-prop all-commute-sequence-Ring
  is-prop-all-commute-sequence-Ring =
    is-prop-type-Prop all-commute-prop-sequence-Ring
```

### The zero sequence is totally central

For any sequence `a : ℕ → R`, `∀ i j : ℕ, 0ᵢ*aⱼ ＝ aⱼ*0ᵢ`.

```agda
module _
  {l : Level} (R : Ring l)
  where abstract

  is-central-zero-sequence-Ring :
    (a : type-sequence-Ring R) →
    all-commute-sequence-Ring R a (zero-sequence-Ring R)
  is-central-zero-sequence-Ring a i j =
    right-zero-law-mul-Ring R _ ∙ inv (left-zero-law-mul-Ring R _)
```
