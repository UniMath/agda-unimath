---
title: Univalent Mathematics in Agda
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundations.empty-type where

open import foundations.levels using (Level; lzero; UU)
```

# The empty type

```agda
data empty : UU lzero where

ind-empty : {l : Level} {P : empty → UU l} → ((x : empty) → P x)
ind-empty ()

ex-falso : {l : Level} {A : UU l} → empty → A
ex-falso = ind-empty

is-empty : {l : Level} → UU l → UU l
is-empty A = A → empty

is-nonempty : {l : Level} → UU l → UU l
is-nonempty A = is-empty (is-empty A)
```
