# Subterminal types

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundation.subterminal-types where

open import foundation.contractible-types using
  ( is-equiv-is-contr; is-contr-is-equiv)
open import foundation.embeddings using (is-emb; is-emb-is-equiv; is-emb-is-emb)
open import foundation.functions using (_∘_)
open import foundation.identity-types using (Id; ap)
open import foundation.propositions using
  ( is-prop; is-proof-irrelevant; all-elements-equal;
    is-proof-irrelevant-all-elements-equal; eq-is-prop'; is-prop-is-contr)
open import foundation.unit-type using (star; terminal-map; is-contr-unit)
open import foundation.universe-levels using (Level; UU)
```

## Idea

A type is said to be subterminal if it embeds into the unit type. A type is subterminal if and only if it is a proposition.

## Definition

```agda
module _
  {l : Level} (A : UU l)
  where
  
  is-subterminal : UU l
  is-subterminal = is-emb (terminal-map {A = A})
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
        ( Id star star)
        ( ap terminal-map)
        ( H x y)
        ( is-prop-is-contr is-contr-unit star star)

  abstract
    eq-is-subterminal : is-subterminal A → all-elements-equal A
    eq-is-subterminal = eq-is-prop' ∘ is-prop-is-subterminal

  abstract
    is-proof-irrelevant-is-subterminal :
      is-subterminal A → is-proof-irrelevant A
    is-proof-irrelevant-is-subterminal H =
      is-proof-irrelevant-all-elements-equal (eq-is-subterminal H)
```
