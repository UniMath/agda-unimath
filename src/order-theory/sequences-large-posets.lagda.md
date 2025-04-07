# Sequences in large posets

```agda
module order-theory.sequences-large-posets where
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

open import order-theory.dependent-products-large-posets
open import order-theory.large-posets
```

</details>

## Idea

A
{{#concept "sequence" Disambiguation="in a large poset" Agda=type-sequence-Large-Poset}}
in a [large poset](order-theory.large-posets.md) is a
[sequence](foundation.sequences.md) in its underlying type.

## Definitions

### The large poset of sequences in large posets

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (P : Large-Poset α β)
  where

  sequence-Large-Poset : Large-Poset α β
  sequence-Large-Poset = Π-Large-Poset (λ (n : ℕ) → P)

  type-sequence-Large-Poset : (l : Level) → UU (α l)
  type-sequence-Large-Poset =
    type-Large-Poset sequence-Large-Poset

  leq-prop-sequence-Large-Poset :
    Large-Relation-Prop β type-sequence-Large-Poset
  leq-prop-sequence-Large-Poset =
    leq-prop-Large-Poset sequence-Large-Poset

  leq-sequence-Large-Poset :
    Large-Relation β type-sequence-Large-Poset
  leq-sequence-Large-Poset =
    leq-Large-Poset sequence-Large-Poset

  is-prop-leq-sequence-Large-Poset :
    is-prop-Large-Relation
      ( type-sequence-Large-Poset)
      ( leq-sequence-Large-Poset)
  is-prop-leq-sequence-Large-Poset =
    is-prop-leq-Large-Poset sequence-Large-Poset

  refl-leq-sequence-Large-Poset :
    is-reflexive-Large-Relation
      ( type-sequence-Large-Poset)
      ( leq-sequence-Large-Poset)
  refl-leq-sequence-Large-Poset =
    refl-leq-Large-Poset sequence-Large-Poset

  transitive-leq-sequence-Large-Poset :
    is-transitive-Large-Relation
      ( type-sequence-Large-Poset)
      ( leq-sequence-Large-Poset)
  transitive-leq-sequence-Large-Poset =
    transitive-leq-Large-Poset sequence-Large-Poset

  antisymmetric-leq-sequence-Large-Poset :
    is-antisymmetric-Large-Relation
      ( type-sequence-Large-Poset)
      ( leq-sequence-Large-Poset)
  antisymmetric-leq-sequence-Large-Poset =
    antisymmetric-leq-Large-Poset sequence-Large-Poset
```
