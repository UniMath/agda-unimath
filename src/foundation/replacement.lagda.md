---
title: The replacement axiom for type theory
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.replacement where

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.embeddings using (id-emb)
open import foundation.homotopies using (refl-htpy)
open import foundation.images using (im)
open import foundation.locally-small-types using (is-locally-small)
open import foundation.surjective-maps using (is-surjective)
open import foundation.universe-levels using (Level; UUω; UU)

open import foundation-core.small-types using
  ( is-small; is-small-equiv'; is-small')
```

## Idea

The type theoretic replacement axiom asserts that the image of a map `f : A → B` from a small type `A` into a locally small type `B` is small.

## Definition

```agda
Replacement : (l : Level) → UUω
Replacement l =
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-small l A → is-locally-small l B → is-small l (im f)

postulate replacement : {l : Level} → Replacement l

replacement-UU :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-locally-small l1 B → is-small l1 (im f)
replacement-UU {l1} {l2} {A} f = replacement f is-small'
```
