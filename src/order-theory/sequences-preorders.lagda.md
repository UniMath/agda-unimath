# Sequences in preorders

```agda
module order-theory.sequences-preorders where
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

open import order-theory.preorders
```

</details>

## Idea

A
{{#concept "sequence" Disambiguation="in a preorder" Agda=sequence-type-Preorder}}
in a [preorder](order-theory.preorders.md) is a
[sequence](foundation.sequences.md) in its underlying type.

## Definitions

### Sequences in preorders

```agda
module _
  {l1 l2 : Level} (P : Preorder l1 l2)
  where

  sequence-type-Preorder : UU l1
  sequence-type-Preorder = sequence (type-Preorder P)
```

### Pointwise comparison on sequences in preorders

```agda
module _
  {l1 l2 : Level} (P : Preorder l1 l2) (u v : sequence-type-Preorder P)
  where

  leq-value-prop-sequence-Preorder : ℕ → Prop l2
  leq-value-prop-sequence-Preorder n = leq-prop-Preorder P (u n) (v n)

  leq-value-sequence-Preorder : ℕ → UU l2
  leq-value-sequence-Preorder = type-Prop ∘ leq-value-prop-sequence-Preorder

  leq-prop-sequence-Preorder : Prop l2
  leq-prop-sequence-Preorder = Π-Prop ℕ leq-value-prop-sequence-Preorder

  leq-sequence-Preorder : UU l2
  leq-sequence-Preorder = type-Prop leq-prop-sequence-Preorder

  is-prop-leq-sequence-Preorder : is-prop leq-sequence-Preorder
  is-prop-leq-sequence-Preorder = is-prop-type-Prop leq-prop-sequence-Preorder
```

## Properties

### The type of sequences in a preorder is a preorder ordered by pointwise comparison

```agda
module _
  {l1 l2 : Level} (P : Preorder l1 l2)
  where

  refl-leq-sequence-Preorder : is-reflexive (leq-sequence-Preorder P)
  refl-leq-sequence-Preorder u n = refl-leq-Preorder P (u n)

  transitive-leq-sequence-Preorder : is-transitive (leq-sequence-Preorder P)
  transitive-leq-sequence-Preorder u v w J I n =
    transitive-leq-Preorder P (u n) (v n) (w n) (J n) (I n)

  sequence-Preorder : Preorder l1 l2
  pr1 sequence-Preorder = sequence-type-Preorder P
  pr1 (pr2 sequence-Preorder) = leq-prop-sequence-Preorder P
  pr1 (pr2 (pr2 sequence-Preorder)) = refl-leq-sequence-Preorder
  pr2 (pr2 (pr2 sequence-Preorder)) = transitive-leq-sequence-Preorder
```
