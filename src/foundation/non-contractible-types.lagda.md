---
title: Univalent Mathematics in Agda
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundation.non-contractible-types where

open import foundation.contractible-types using (is-contr; center; contraction)
open import foundation.empty-type using (is-empty; empty)
open import foundation.functions using (id)
open import foundation.levels using (Level; UU)
open import foundation.negation using (¬)
```

```agda
is-not-contractible : {l : Level} → UU l → UU l
is-not-contractible X = ¬ (is-contr X)
```

```agda
is-not-contractible-is-empty :
  {l : Level} {X : UU l} → is-empty X → is-not-contractible X
is-not-contractible-is-empty H C = H (center C)

is-not-contractible-empty : is-not-contractible empty
is-not-contractible-empty = is-not-contractible-is-empty id
```
