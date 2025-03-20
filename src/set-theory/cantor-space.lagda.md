# Cantor space

```agda
open import foundation.function-extensionality-axiom

module
  set-theory.cantor-space
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.booleans funext
open import foundation.coproduct-types funext
open import foundation.dependent-pair-types
open import foundation.empty-types funext
open import foundation.lawveres-fixed-point-theorem funext
open import foundation.negation funext
open import foundation.propositional-truncations funext
open import foundation.sets funext
open import foundation.tight-apartness-relations funext
open import foundation.unit-type
open import foundation.universe-levels

open import set-theory.cantors-diagonal-argument funext
open import set-theory.countable-sets funext
open import set-theory.uncountable-sets funext

open import univalent-combinatorics.equality-standard-finite-types funext
open import univalent-combinatorics.standard-finite-types funext
```

</details>

## Idea

The
{{#concept "Cantor space" Disambiguation="as a type" Agda=cantor-space WD="Cantor space" WDID=Q616653}}
is the [set](foundation-core.sets.md) of
[functions](foundation-core.function-types.md) `ℕ → Fin 2`. In other words, it
is the set of [binary](foundation.booleans.md)
[sequences](foundation.sequences.md).

## Definition

```agda
cantor-space : UU lzero
cantor-space = ℕ → Fin 2
```

## Properties

### The cantor space has a tight apartness relation

```agda
cantor-space-Type-With-Tight-Apartness : Type-With-Tight-Apartness lzero lzero
cantor-space-Type-With-Tight-Apartness =
  exp-Type-With-Tight-Apartness ℕ (Fin-Type-With-Tight-Apartness 2)
```

### The cantor space is a set

```agda
is-set-cantor-space : is-set cantor-space
is-set-cantor-space = is-set-function-type (is-set-Fin 2)

cantor-space-Set : Set lzero
cantor-space-Set = (cantor-space , is-set-cantor-space)
```

### The cantor space is uncountable

```agda
is-uncountable-cantor-space : is-uncountable cantor-space-Set
is-uncountable-cantor-space =
  is-uncountable-sequence-discrete-type-diagonal-argument-Cantor
    ( Fin-Discrete-Type 2)
    ( inr star)
    ( inl (inr star))
    ( neq-inr-inl)
```

## External links

- [Cantor space](https://en.wikipedia.org/wiki/Cantor_space) at Wikipedia
- [Cantor space](https://ncatlab.org/nlab/show/Cantor+space) at $n$Lab
