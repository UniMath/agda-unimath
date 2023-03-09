# Tuples of types

```agda
module foundation.tuples-of-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.universe-levels

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

An `n`-tuple of types is a type family `Fin n → UU`.

## Definition

```agda
tuple-types : (l : Level) (n : ℕ) → UU (lsuc l)
tuple-types l n = Fin n → UU l
```

## Properties

### The tuple of types `A j` for `i ≠ j`, given `i`.

```agda
{-
tuple-types-complement-point :
  {l : Level} {n : ℕ} (A : tuple-types l (succ-ℕ n)) (i : Fin (succ-ℕ n)) →
  tuple-types l n
tuple-types-complement-point A i = {!!}
-}
```

-- Σ (x : Fin (n + 1)) (a ≠ x)
   ≃
-- Fin n
