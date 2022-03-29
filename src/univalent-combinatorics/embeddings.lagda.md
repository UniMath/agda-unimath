---
title: Injective maps
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.embeddings where

open import foundation.embeddings public

open import foundation.decidable-types using (is-decidable; is-decidable-iff)
open import foundation.universe-levels using (Level; UU)

open import univalent-combinatorics.equality-finite-types using
  ( is-set-is-finite)
open import univalent-combinatorics.finite-types using (is-finite)
open import univalent-combinatorics.injective-maps using
  ( is-emb-is-injective; is-injective-is-emb;
    is-decidable-is-injective-is-finite)
```

## Idea

Embeddings in the presence of finite types enjoy further properties.

## Properties

```agda
is-decidable-is-emb-is-finite :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-finite A → is-finite B → is-decidable (is-emb f)
is-decidable-is-emb-is-finite f HA HB =
  is-decidable-iff
    ( is-emb-is-injective (is-set-is-finite HB))
    ( is-injective-is-emb)
    ( is-decidable-is-injective-is-finite f HA HB)
```
