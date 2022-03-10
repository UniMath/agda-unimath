# Iterated loop spaces

```agda
{-# OPTIONS --without-K --exact-split #-}

module synthetic-homotopy-theory.iterated-loop-spaces where

open import elementary-number-theory.natural-numbers using (ℕ; zero-ℕ; succ-ℕ)

open import foundation.identity-types using (Id; refl)
open import foundation.universe-levels using (Level; UU)

open import synthetic-homotopy-theory.loop-spaces using (Ω)
open import synthetic-homotopy-theory.pointed-types using (Pointed-Type)
```

```agda
module _
  {l : Level}
  where

  iterated-loop-space : ℕ → Pointed-Type l → Pointed-Type l
  iterated-loop-space zero-ℕ A = A
  iterated-loop-space (succ-ℕ n) A = Ω (iterated-loop-space n A)
  
  Ω² : Pointed-Type l → Pointed-Type l
  Ω² A = iterated-loop-space 2 A
  
  type-Ω² : {A : UU l} (a : A) → UU l
  type-Ω² a = Id (refl {x = a}) (refl {x = a})
  
  refl-Ω² : {A : UU l} {a : A} → type-Ω² a
  refl-Ω² = refl
  
  Ω³ : Pointed-Type l → Pointed-Type l
  Ω³ A = iterated-loop-space 3 A
  
  type-Ω³ : {A : UU l} (a : A) → UU l
  type-Ω³ a = Id (refl-Ω² {a = a}) (refl-Ω² {a = a})
  
  refl-Ω³ : {A : UU l} {a : A} → type-Ω³ a
  refl-Ω³ = refl
```
