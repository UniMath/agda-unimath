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
open import foundation.universe-levels

open import lists.sequences

open import order-theory.posets
open import order-theory.sequences-preorders
```

</details>

## Idea

A {{#concept "sequence" Disambiguation="in a poset" Agda=sequence-type-Poset}}
in a [poset](order-theory.posets.md) is a [sequence](lists.sequences.md) in its
underlying type.

## Definitions

### Sequences in partially ordered sets

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2)
  where

  sequence-type-Poset : UU l1
  sequence-type-Poset = sequence-type-Preorder (preorder-Poset P)
```

### Pointwise comparison on sequences in partially ordered sets

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2)
  where

  leq-value-prop-sequence-Poset :
    (u v : sequence-type-Poset P) → ℕ → Prop l2
  leq-value-prop-sequence-Poset =
    leq-value-prop-sequence-Preorder (preorder-Poset P)

  leq-value-sequence-Poset :
    (u v : sequence-type-Poset P) → ℕ → UU l2
  leq-value-sequence-Poset =
    leq-value-sequence-Preorder (preorder-Poset P)

  leq-prop-sequence-Poset : (u v : sequence-type-Poset P) → Prop l2
  leq-prop-sequence-Poset =
    leq-prop-sequence-Preorder (preorder-Poset P)

  leq-sequence-Poset : (u v : sequence-type-Poset P) → UU l2
  leq-sequence-Poset =
    leq-sequence-Preorder (preorder-Poset P)

  is-prop-leq-sequence-Poset :
    (u v : sequence-type-Poset P) →
    is-prop (leq-sequence-Poset u v)
  is-prop-leq-sequence-Poset =
    is-prop-leq-sequence-Preorder (preorder-Poset P)
```

## Properties

### The type of sequences in a poset is a poset ordered by pointwise comparison

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2)
  where

  antisymmetric-leq-sequence-Poset : is-antisymmetric (leq-sequence-Poset P)
  antisymmetric-leq-sequence-Poset u v I J =
    eq-htpy (λ n → antisymmetric-leq-Poset P (u n) (v n) (I n) (J n))

  sequence-Poset : Poset l1 l2
  pr1 sequence-Poset = sequence-Preorder (preorder-Poset P)
  pr2 sequence-Poset = antisymmetric-leq-sequence-Poset

  refl-leq-sequence-Poset : is-reflexive (leq-sequence-Poset P)
  refl-leq-sequence-Poset =
    refl-leq-Poset sequence-Poset

  transitive-leq-sequence-Poset : is-transitive (leq-sequence-Poset P)
  transitive-leq-sequence-Poset =
    transitive-leq-Poset sequence-Poset
```
