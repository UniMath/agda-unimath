---
title: Univalent Mathematics in Agda
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundations.decidable-types where

open import foundations.levels using (UU; Level)
open import foundations.coproduct-types using (coprod; inl; inr)
open import foundations.negation using (¬; ¬¬; functor-neg)
open import foundations.empty-type using (ex-falso)
```

## Decidable types

```agda
dn-elim-is-decidable :
  {l : Level} (P : UU l) → coprod P (¬ P) → (¬¬ P → P)
dn-elim-is-decidable P (inl x) p = x
dn-elim-is-decidable P (inr x) p = ex-falso (p x)

dn-is-decidable : {l : Level} {P : UU l} → ¬¬ (coprod P (¬ P))
dn-is-decidable {P = P} f =
  functor-neg (inr {A = P} {B = ¬ P}) f
    ( functor-neg (inl {A = P} {B = ¬ P}) f)
```
