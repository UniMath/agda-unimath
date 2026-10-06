# Mutually centralizing sequences in rings

```agda
module ring-theory.mutually-centralizing-sequences-rings where
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

open import ring-theory.rings
open import ring-theory.sequences-rings
```

</details>

## Idea

Two [sequences](ring-theory.sequences-rings.md) `a`, `b` in a
[ring](ring-theory.rings.md) are called
{{#concept "mutually centralizing" Disambiguation="sequences in a ring" Agda=is-mutually-centralizing-sequence-Ring}}
if `aᵢbⱼ ＝ bⱼaᵢ` for all `i j : ℕ`.

## Definition

### Mutually centralizing sequences in a ring

```agda
module _
  {l : Level} (R : Ring l) (a b : type-sequence-Ring R)
  where

  is-mutually-centralizing-prop-sequence-Ring : Prop l
  is-mutually-centralizing-prop-sequence-Ring =
    Π-Prop
      ( ℕ)
      ( λ i →
        Π-Prop
          ( ℕ)
          ( λ j →
            commute-prop-Monoid
              ( multiplicative-monoid-Ring R)
              ( a i)
              ( b j)))

  is-mutually-centralizing-sequence-Ring : UU l
  is-mutually-centralizing-sequence-Ring =
    type-Prop is-mutually-centralizing-prop-sequence-Ring

  is-prop-is-mutually-centralizing-sequence-Ring :
    is-prop is-mutually-centralizing-sequence-Ring
  is-prop-is-mutually-centralizing-sequence-Ring =
    is-prop-type-Prop is-mutually-centralizing-prop-sequence-Ring
```

## Properties

### The zero sequence is mutually centralizing with all sequences

For any sequence `a : ℕ → R`, `∀ i j : ℕ, 0ᵢ*aⱼ ＝ aⱼ*0ᵢ`.

```agda
module _
  {l : Level} (R : Ring l)
  where abstract

  is-mutually-centralizing-zero-sequence-Ring :
    (a : type-sequence-Ring R) →
    is-mutually-centralizing-sequence-Ring R a (zero-sequence-Ring R)
  is-mutually-centralizing-zero-sequence-Ring a i j =
    right-zero-law-mul-Ring R _ ∙ inv (left-zero-law-mul-Ring R _)
```
