---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split --safe --no-import-sorts #-}

module foundations.00-preamble where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_) renaming (Set to UU) public

data raise (l : Level) {l1 : Level} (A : UU l1) : UU (l1 ⊔ l) where
  map-raise : A → raise l A

map-inv-raise : {l l1 : Level} {A : UU l1} → raise l A → A
map-inv-raise (map-raise x) = x
```
