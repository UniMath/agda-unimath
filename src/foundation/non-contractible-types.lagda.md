# Non-contractible types

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundation.non-contractible-types where

open import foundation.contractible-types using (is-contr; center; contraction)
open import foundation.empty-types using (is-empty; empty)
open import foundation.functions using (id)
open import foundation.negation using (¬)
open import foundation.universe-levels using (Level; UU)
```

## Idea

A type `X` is non-contractible if it comes equipped with an element of type `¬ (is-contr X)`.

## Definition

```agda
is-not-contractible : {l : Level} → UU l → UU l
is-not-contractible X = ¬ (is-contr X)
```

## Properties

### Empty types are non-contractible

```agda
is-not-contractible-is-empty :
  {l : Level} {X : UU l} → is-empty X → is-not-contractible X
is-not-contractible-is-empty H C = H (center C)

is-not-contractible-empty : is-not-contractible empty
is-not-contractible-empty = is-not-contractible-is-empty id
```
