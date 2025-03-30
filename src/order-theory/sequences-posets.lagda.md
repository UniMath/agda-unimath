# Sequences in partially ordered sets

```agda
module order-theory.sequences-posets where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.propositions
open import foundation.sequences
open import foundation.universe-levels

open import order-theory.posets
```

</details>

## Idea

A {{#concept "sequence" Disambiguation="in a poset" Agda=sequence-Poset}} in a
[poset](order-theory.posets.md) is a [sequence](foundation.sequences.md) in its
underlying type.

## Definitions

### Sequences in partially ordered sets

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2)
  where

  type-sequence-Poset : UU l1
  sequence-Poset = sequence (type-Poset P)
```

### Pointwise comparison on sequences in partially ordered sets

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2) (u v : sequence-Poset P)
  where

  leq-value-prop-sequence-Poset : ℕ → Prop l2
  leq-value-prop-sequence-Poset n = leq-prop-Poset P (u n) (v n)

  leq-value-sequence-Poset : ℕ → UU l2
  leq-value-sequence-Poset = type-Prop ∘ leq-value-prop-sequence-Poset

  leq-prop-sequence-Poset : Prop l2
  leq-prop-sequence-Poset = Π-Prop ℕ leq-value-prop-sequence-Poset

  leq-sequence-Poset : UU l2
  leq-sequence-Poset = type-Prop leq-prop-sequence-Poset

  is-prop-leq-sequence-Poset : is-prop leq-sequence-Poset
  is-prop-leq-sequence-Poset = is-prop-type-Prop leq-prop-sequence-Poset
```

## Properties

### The type of sequences in a poset is a poset ordered by pointwise comparison

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2)
  where

  sequence-Poset : Poset l1 l2
  pr1 (pr1 poset-sequence-Poset) = sequence-Poset P
  pr1 (pr2 (pr1 poset-sequence-Poset)) = leq-prop-sequence-Poset P
  pr1 (pr2 (pr2 (pr1 poset-sequence-Poset))) u n = refl-leq-Poset P (u n)
  pr2 (pr2 (pr2 (pr1 poset-sequence-Poset))) u v w J I n =
    transitive-leq-Poset P (u n) (v n) (w n) (J n) (I n)
  pr2 poset-sequence-Poset u v I J =
    eq-htpy (λ n → antisymmetric-leq-Poset P (u n) (v n) (I n) (J n))

  refl-leq-sequence-Poset : is-reflexive (leq-sequence-Poset P)
  refl-leq-sequence-Poset = refl-leq-Poset poset-sequence-Poset

  transitive-leq-sequence-Poset : is-transitive (leq-sequence-Poset P)
  transitive-leq-sequence-Poset = transitive-leq-Poset poset-sequence-Poset

  antisymmetric-leq-sequence-Poset : is-antisymmetric (leq-sequence-Poset P)
  antisymmetric-leq-sequence-Poset =
    antisymmetric-leq-Poset poset-sequence-Poset
```
