# Mutually centralizing sequences in semirings

```agda
module ring-theory.mutually-centralizing-sequences-semirings where
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

open import ring-theory.semirings
open import ring-theory.sequences-semirings
```

</details>

## Idea

Two [sequences](ring-theory.sequences-semirings.md) `a`, `b` in a
[semiring](ring-theory.semirings.md) are called
{{#concept "mutually centralizing" Disambiguation="sequences in a semiring" Agda=is-mutually-centralizing-sequence-Semiring}}
if `aᵢbⱼ ＝ bⱼaᵢ` for all `i j : ℕ`.

## Definition

### Mutually centralizing sequences in a semiring

```agda
module _
  {l : Level} (R : Semiring l) (a b : type-sequence-Semiring R)
  where

  is-mutually-centralizing-prop-sequence-Semiring : Prop l
  is-mutually-centralizing-prop-sequence-Semiring =
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

  is-mutually-centralizing-sequence-Semiring : UU l
  is-mutually-centralizing-sequence-Semiring =
    type-Prop is-mutually-centralizing-prop-sequence-Semiring

  is-prop-is-mutually-centralizing-sequence-Semiring :
    is-prop is-mutually-centralizing-sequence-Semiring
  is-prop-is-mutually-centralizing-sequence-Semiring =
    is-prop-type-Prop is-mutually-centralizing-prop-sequence-Semiring
```

## Properties

### The zero sequence is mutually centralizing with all sequences

For any sequence `a : ℕ → R`, `∀ i j : ℕ, 0ᵢ*aⱼ ＝ aⱼ*0ᵢ`.

```agda
module _
  {l : Level} (R : Semiring l)
  where abstract

  is-mutually-centralizing-zero-sequence-Semiring :
    (a : type-sequence-Semiring R) →
    is-mutually-centralizing-sequence-Semiring R a (zero-sequence-Semiring R)
  is-mutually-centralizing-zero-sequence-Semiring a i j =
    right-zero-law-mul-Semiring R _ ∙ inv (left-zero-law-mul-Semiring R _)
```
