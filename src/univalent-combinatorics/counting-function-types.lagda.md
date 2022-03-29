---
title: Counting the elements of function types
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.counting-function-types where

open import foundation.universe-levels using (Level; UU)

open import univalent-combinatorics.counting using (count)
open import univalent-combinatorics.counting-dependent-function-types using
  ( count-Π)
```

```agda
count-function-type :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  count A → count B → count (A → B)
count-function-type e f =
  count-Π e (λ x → f)
```
