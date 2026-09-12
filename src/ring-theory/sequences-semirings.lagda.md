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

## Properties

### Totally commuting sequences in a semiring

Two sequences `a`, `b` are called **totally commuting** if `aᵢbⱼ ＝ bⱼaᵢ` for
all `i j : ℕ`.

```agda
module _
  {l : Level} (R : Semiring l) (a b : type-sequence-Semiring R)
  where

  all-commute-prop-sequence-Semiring : Prop l
  all-commute-prop-sequence-Semiring =
    Π-Prop
      ( ℕ)
      ( λ i →
        Π-Prop
          ( ℕ)
          ( λ j →
            commute-prop-Monoid
              ( multiplicative-monoid-Semiring R)
              ( a i)
              ( b j)))

  all-commute-sequence-Semiring : UU l
  all-commute-sequence-Semiring = type-Prop all-commute-prop-sequence-Semiring

  is-prop-all-commute-sequence-Semiring : is-prop all-commute-sequence-Semiring
  is-prop-all-commute-sequence-Semiring =
    is-prop-type-Prop all-commute-prop-sequence-Semiring
```

### The zero sequence is totally central

For any sequence `a : ℕ → R`, `∀ i j : ℕ, 0ᵢ*aⱼ ＝ aⱼ*0ᵢ`.

```agda
module _
  {l : Level} (R : Semiring l)
  where abstract

  is-central-zero-sequence-Semiring :
    (a : type-sequence-Semiring R) →
    all-commute-sequence-Semiring R a (zero-sequence-Semiring R)
  is-central-zero-sequence-Semiring a i j =
    right-zero-law-mul-Semiring R _ ∙ inv (left-zero-law-mul-Semiring R _)
```
