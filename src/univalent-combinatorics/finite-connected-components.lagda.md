# Finiteness of the type of connected components

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.finite-connected-components where

open import elementary-number-theory.natural-numbers using (ℕ)

open import foundation.propositions using (UU-Prop; type-Prop)
open import foundation.set-truncations using (type-trunc-Set)
open import foundation.universe-levels using (Level; UU)

open import univalent-combinatorics.finite-types using
  ( is-finite-Prop; has-cardinality-Prop)
```

## Idea

A type is said to have finitely many connected components if its set truncation is a finite type.

## Definition

```agda
has-finitely-many-components-Prop : {l : Level} → UU l → UU-Prop l
has-finitely-many-components-Prop A = is-finite-Prop (type-trunc-Set A)

has-finitely-many-components : {l : Level} → UU l → UU l
has-finitely-many-components A = type-Prop (has-finitely-many-components-Prop A)

has-cardinality-components-Prop : {l : Level} (k : ℕ) → UU l → UU-Prop l
has-cardinality-components-Prop k A =
  has-cardinality-Prop k (type-trunc-Set A)

has-cardinality-components : {l : Level} (k : ℕ) → UU l → UU l
has-cardinality-components k A =
  type-Prop (has-cardinality-components-Prop k A)
```
