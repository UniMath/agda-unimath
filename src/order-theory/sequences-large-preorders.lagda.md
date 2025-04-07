# Sequences in large preorders

```agda
module order-theory.sequences-large-preorders where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.binary-relations
open import foundation.constant-maps
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.large-binary-relations
open import foundation.propositions
open import foundation.sequences
open import foundation.universe-levels

open import order-theory.dependent-products-large-preorders
open import order-theory.large-preorders
```

</details>

## Idea

A
{{#concept "sequence" Disambiguation="in a large preorder" Agda=type-sequence-Large-Preorder}}
in a [large preorder](order-theory.large-preorders.md) is a
[sequence](foundation.sequences.md) in its underlying type.

## Definitions

### The large preorder of sequences in large preorders

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (P : Large-Preorder α β)
  where

  sequence-Large-Preorder : Large-Preorder α β
  sequence-Large-Preorder = Π-Large-Preorder (λ (n : ℕ) → P)

  type-sequence-Large-Preorder : (l : Level) → UU (α l)
  type-sequence-Large-Preorder =
    type-Large-Preorder sequence-Large-Preorder

  leq-prop-sequence-Large-Preorder :
    Large-Relation-Prop β type-sequence-Large-Preorder
  leq-prop-sequence-Large-Preorder =
    leq-prop-Large-Preorder sequence-Large-Preorder

  leq-sequence-Large-Preorder :
    Large-Relation β type-sequence-Large-Preorder
  leq-sequence-Large-Preorder =
    leq-Large-Preorder sequence-Large-Preorder

  is-prop-leq-sequence-Large-Preorder :
    is-prop-Large-Relation
      ( type-sequence-Large-Preorder)
      ( leq-sequence-Large-Preorder)
  is-prop-leq-sequence-Large-Preorder =
    is-prop-leq-Large-Preorder sequence-Large-Preorder

  refl-leq-sequence-Large-Preorder :
    is-reflexive-Large-Relation
      ( type-sequence-Large-Preorder)
      ( leq-sequence-Large-Preorder)
  refl-leq-sequence-Large-Preorder =
    refl-leq-Large-Preorder sequence-Large-Preorder

  transitive-leq-sequence-Large-Preorder :
    is-transitive-Large-Relation
      ( type-sequence-Large-Preorder)
      ( leq-sequence-Large-Preorder)
  transitive-leq-sequence-Large-Preorder =
    transitive-leq-Large-Preorder sequence-Large-Preorder
```
