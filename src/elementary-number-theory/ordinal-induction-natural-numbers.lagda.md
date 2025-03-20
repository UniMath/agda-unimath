# The ordinal induction principle for the natural numbers

```agda
open import foundation.function-extensionality-axiom

module
  elementary-number-theory.ordinal-induction-natural-numbers
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers funext

open import foundation.empty-types funext
open import foundation.universe-levels
```

</details>

## Idea

The **ordinal induction principle of the natural numbers** is the well-founded
induction principle of ℕ.

## To Do

The computation rule should still be proven.

```agda
□-<-ℕ :
  {l : Level} → (ℕ → UU l) → ℕ → UU l
□-<-ℕ P n = (m : ℕ) → (le-ℕ m n) → P m

reflect-□-<-ℕ :
  {l : Level} (P : ℕ → UU l) →
  (( n : ℕ) → □-<-ℕ P n) → (n : ℕ) → P n
reflect-□-<-ℕ P f n = f (succ-ℕ n) n (succ-le-ℕ n)

zero-ordinal-ind-ℕ :
  { l : Level} (P : ℕ → UU l) → □-<-ℕ P zero-ℕ
zero-ordinal-ind-ℕ P m t = ex-falso (contradiction-le-zero-ℕ m t)

succ-ordinal-ind-ℕ :
  {l : Level} (P : ℕ → UU l) → ((n : ℕ) → (□-<-ℕ P n) → P n) →
  (k : ℕ) → □-<-ℕ P k → □-<-ℕ P (succ-ℕ k)
succ-ordinal-ind-ℕ P f k g m t =
  f m (λ m' t' → g m' (transitive-le-ℕ' m' m k t' t))

induction-ordinal-ind-ℕ :
  { l : Level} (P : ℕ → UU l) →
  ( qS : (k : ℕ) → □-<-ℕ P k → □-<-ℕ P (succ-ℕ k))
  ( n : ℕ) → □-<-ℕ P n
induction-ordinal-ind-ℕ P qS zero-ℕ = zero-ordinal-ind-ℕ P
induction-ordinal-ind-ℕ P qS (succ-ℕ n) =
  qS n (induction-ordinal-ind-ℕ P qS n)

ordinal-ind-ℕ :
  { l : Level} (P : ℕ → UU l) →
  ( (n : ℕ) → (□-<-ℕ P n) → P n) →
  ( n : ℕ) → P n
ordinal-ind-ℕ P f =
  reflect-□-<-ℕ P
    ( induction-ordinal-ind-ℕ P (succ-ordinal-ind-ℕ P f))
```
