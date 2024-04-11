# Subterminal types

```agda
module foundation.subterminal-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.embeddings
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.propositions
```

</details>

## Idea

A type is said to be {{#concept "subterminal" Agda=is-subterminal}} if it
[embeds](foundation-core.embeddings.md) into the
[unit type](foundation.unit-type.md). A type is subterminal if and only if it is
a [proposition](foundation-core.propositions.md).

## Definition

```agda
module _
  {l : Level} (A : UU l)
  where

  is-subterminal : UU l
  is-subterminal = is-emb (terminal-map A)
```

## Properties

### A type is subterminal if and only if it is a proposition

```agda
module _
  {l : Level} {A : UU l}
  where

  abstract
    is-subterminal-is-proof-irrelevant :
      is-proof-irrelevant A → is-subterminal A
    is-subterminal-is-proof-irrelevant H =
      is-emb-is-emb
        ( λ x → is-emb-is-equiv (is-equiv-is-contr _ (H x) is-contr-unit))

  abstract
    is-subterminal-all-elements-equal : all-elements-equal A → is-subterminal A
    is-subterminal-all-elements-equal =
      is-subterminal-is-proof-irrelevant ∘
      is-proof-irrelevant-all-elements-equal

  abstract
    is-subterminal-is-prop : is-prop A → is-subterminal A
    is-subterminal-is-prop = is-subterminal-all-elements-equal ∘ eq-is-prop'

  abstract
    is-prop-is-subterminal : is-subterminal A → is-prop A
    is-prop-is-subterminal H x y =
      is-contr-is-equiv
        ( star ＝ star)
        ( ap (terminal-map A))
        ( H x y)
        ( is-prop-unit star star)

  abstract
    eq-is-subterminal : is-subterminal A → all-elements-equal A
    eq-is-subterminal = eq-is-prop' ∘ is-prop-is-subterminal

  abstract
    is-proof-irrelevant-is-subterminal :
      is-subterminal A → is-proof-irrelevant A
    is-proof-irrelevant-is-subterminal H =
      is-proof-irrelevant-all-elements-equal (eq-is-subterminal H)
```

## Table of files about propositional logic

The following table gives an overview of basic constructions in propositional
logic and related considerations.

{{#include tables/propositional-logic.md}}
