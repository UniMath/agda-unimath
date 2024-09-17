# Baire space

```agda
module set-theory.baire-space where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.lawveres-fixed-point-theorem
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.sets
open import foundation.universe-levels

open import foundation-core.empty-types
open import foundation-core.identity-types
open import foundation-core.propositions

open import set-theory.countable-sets
open import set-theory.uncountable-sets
```

</details>

## Idea

The {{#concept "Baire space" Agda=baire-space}} is the
[set](foundation-core.sets.md) of [functions](foundation-core.function-types.md)
`ℕ → ℕ`. In other words, it is the set of
[infinite sequences](foundation.sequences.md) of
[natural numbers](elementary-number-theory.natural-numbers.md).

## Definition

```agda
baire-space : UU lzero
baire-space = ℕ → ℕ
```

## Properties

### The Baire space is a set

```agda
is-set-baire-space : is-set baire-space
is-set-baire-space = is-set-function-type is-set-ℕ

baire-space-Set : Set lzero
baire-space-Set = (baire-space , is-set-baire-space)
```

### The Baire space is uncountable

```agda
is-uncountable-baire-space : is-uncountable baire-space-Set
is-uncountable-baire-space P =
  apply-universal-property-trunc-Prop
    ( is-directly-countable-is-countable baire-space-Set succ-ℕ P)
    ( empty-Prop)
    ( λ H →
      apply-universal-property-trunc-Prop
        ( fixed-point-theorem-Lawvere (pr2 H) succ-ℕ)
        ( empty-Prop)
        ( λ F →
          reductio-ad-absurdum (pr2 F) (has-no-fixed-points-succ-ℕ (pr1 F))))
```

## External links

- [Baire space (set theory)](<https://en.wikipedia.org/wiki/Baire_space_(set_theory)>)
  at Wikipedia
- [Baire space of sequences](https://ncatlab.org/nlab/show/Baire+space+of+sequences)
  at $n$Lab
