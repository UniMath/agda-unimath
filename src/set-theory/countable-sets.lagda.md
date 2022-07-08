---
title: Countable sets
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module set-theory.countable-sets where

open import elementary-number-theory.natural-numbers

open import foundation.existential-quantification
open import foundation.maybe
open import foundation.propositions
open import foundation.surjective-maps
open import foundation.universe-levels
```

```agda
is-countable-Prop : {l : Level} → UU l → UU-Prop l
is-countable-Prop X = ∃-Prop (ℕ → Maybe X) is-surjective

is-countable : {l : Level} → UU l → UU l
is-countable X = type-Prop (is-countable-Prop X)

is-prop-is-countable : {l : Level} (X : UU l) → is-prop (is-countable X)
is-prop-is-countable X = is-prop-type-Prop (is-countable-Prop X)
```
