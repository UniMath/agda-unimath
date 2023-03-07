# Iterated loop spaces

```agda
module synthetic-homotopy-theory.iterated-loop-spaces where
```

<details><summary>Imports</summary>

```agda
open import synthetic-homotopy-theory.loop-spaces
open import foundation.identity-types
open import foundation.universe-levels
open import elementary-number-theory.natural-numbers
open import structured-types.pointed-types
```

</details>

```agda
module _
  {l : Level}
  where

  iterated-loop-space : ℕ → Pointed-Type l → Pointed-Type l
  iterated-loop-space zero-ℕ A = A
  iterated-loop-space (succ-ℕ n) A = Ω (iterated-loop-space n A)
```
