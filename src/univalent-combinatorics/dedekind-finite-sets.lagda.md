---
title: Dedekind finite sets
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.dedekind-finite-sets where

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.embeddings using (is-emb)
open import foundation.equivalences using (is-equiv; is-equiv-Prop)
open import foundation.propositions using
  (Prop; Π-Prop; function-Prop; type-Prop)
open import foundation.sets using (Set; type-Set; is-set-type-Set; is-set)
open import foundation.universe-levels using (Level; UU; lsuc)
```

## Idea

Dedekind finite sets are sets `X` with the property that every embedding `X ↪ X` is an equivalence.

## Definition

```agda
is-dedekind-finite-set-Prop : {l : Level} → Set l → Prop l
is-dedekind-finite-set-Prop X =
  Π-Prop
    ( type-Set X → type-Set X)
    ( λ f → function-Prop (is-emb f) (is-equiv-Prop f))

is-dedekind-finite-set : {l : Level} → Set l → UU l
is-dedekind-finite-set X = type-Prop (is-dedekind-finite-set-Prop X)

𝔽-Dedekind : (l : Level) → UU (lsuc l)
𝔽-Dedekind l = Σ (Set l) is-dedekind-finite-set

module _
  {l : Level} (X : 𝔽-Dedekind l)
  where

  set-𝔽-Dedekind : Set l
  set-𝔽-Dedekind = pr1 X

  type-𝔽-Dedekind : UU l
  type-𝔽-Dedekind = type-Set set-𝔽-Dedekind

  is-set-type-𝔽-Dedekind : is-set type-𝔽-Dedekind
  is-set-type-𝔽-Dedekind = is-set-type-Set set-𝔽-Dedekind

  is-dedekind-finite-set-𝔽-Dedekind : is-dedekind-finite-set set-𝔽-Dedekind
  is-dedekind-finite-set-𝔽-Dedekind = pr2 X
```
