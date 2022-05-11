# Iterated loop spaces

```agda
{-# OPTIONS --without-K --exact-split #-}

module synthetic-homotopy-theory.iterated-loop-spaces where

open import elementary-number-theory.natural-numbers using (ℕ; zero-ℕ; succ-ℕ)

open import foundation.identity-types using (Id; refl)
open import foundation.universe-levels using (Level; UU)

open import structured-types.pointed-types using (Pointed-Type)

open import synthetic-homotopy-theory.loop-spaces using (Ω)
```

```agda
module _
  {l : Level}
  where

  iterated-loop-space : ℕ → Pointed-Type l → Pointed-Type l
  iterated-loop-space zero-ℕ A = A
  iterated-loop-space (succ-ℕ n) A = Ω (iterated-loop-space n A)
```
