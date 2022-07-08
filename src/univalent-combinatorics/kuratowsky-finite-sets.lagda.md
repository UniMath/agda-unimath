---
title: Kuratowsky finite sets
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.kuratowsky-finite-sets where

open import elementary-number-theory.natural-numbers using (ℕ)

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.existential-quantification using (∃-Prop)
open import foundation.propositions using (UU-Prop; type-Prop)
open import foundation.sets using (UU-Set; type-Set; is-set-type-Set; is-set)
open import foundation.surjective-maps using (is-surjective)
open import foundation.universe-levels using (Level; UU; lsuc)

open import univalent-combinatorics.standard-finite-types using (Fin)
```

## Idea

A Kuratowsky finite type is a set `X` for which there exists a surjection into `X` from a standard finite type. In other words, the Kuratowsky finite types are the set-quotient of a standard finite type.

## Definition

```agda
is-kuratowsky-finite-set-Prop : {l : Level} → UU-Set l → UU-Prop l
is-kuratowsky-finite-set-Prop X =
  ∃-Prop ℕ (λ n → Σ (Fin n → type-Set X) is-surjective)

is-kuratowsky-finite-set : {l : Level} → UU-Set l → UU l
is-kuratowsky-finite-set X = type-Prop (is-kuratowsky-finite-set-Prop X)

𝔽-Kuratowsky : (l : Level) → UU (lsuc l)
𝔽-Kuratowsky l = Σ (UU-Set l) is-kuratowsky-finite-set

module _
  {l : Level} (X : 𝔽-Kuratowsky l)
  where

  set-𝔽-Kuratowsky : UU-Set l
  set-𝔽-Kuratowsky = pr1 X

  type-𝔽-Kuratowsky : UU l
  type-𝔽-Kuratowsky = type-Set set-𝔽-Kuratowsky

  is-set-type-𝔽-Kuratowsky : is-set type-𝔽-Kuratowsky
  is-set-type-𝔽-Kuratowsky = is-set-type-Set set-𝔽-Kuratowsky

  is-kuratowsky-finite-set-𝔽-Kuratowsky :
    is-kuratowsky-finite-set set-𝔽-Kuratowsky
  is-kuratowsky-finite-set-𝔽-Kuratowsky = pr2 X
```
