---
title: Uncountable sets
___

```agda
{-# OPTIONS --without-K --exact-split #-}

module set-theory.uncountable-sets where

open import foundation.negation
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import set-theory.countable-sets
```

## Definition

```agda
is-uncountable-Prop : {l : Level} → UU-Set l → UU-Prop l
is-uncountable-Prop X = neg-Prop (is-countable-Prop X)

is-uncountable : {l : Level} → UU-Set l → UU l
is-uncountable X = type-Prop (is-uncountable-Prop X)

is-prop-is-uncountable : {l : Level} (X : UU-Set l) → is-prop (is-uncountable X)
is-prop-is-uncountable X = is-prop-type-Prop (is-uncountable-Prop X)
```
