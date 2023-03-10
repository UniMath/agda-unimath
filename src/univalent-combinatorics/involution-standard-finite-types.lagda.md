# An involution on the standard finite types

```agda
module univalent-combinatorics.involution-standard-finite-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.modular-arithmetic-standard-finite-types
open import elementary-number-theory.natural-numbers

open import foundation.identity-types
open import foundation.involutions

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Every standard finite type `Fin k` has an involution operation given by `x ↦ -x - 1`, using the group operations on `Fin k`.

## Definition

```agda
opposite-Fin : (k : ℕ) → Fin k → Fin k
opposite-Fin k x = pred-Fin k (neg-Fin k x)
```

## Properties

### The opposite function on `Fin k` is an involution

```agda
is-involution-opposite-Fin : (k : ℕ) → is-involution (opposite-Fin k)
is-involution-opposite-Fin k x =
  ( ap (pred-Fin k) (neg-pred-Fin k (neg-Fin k x))) ∙
  ( ( isretr-pred-Fin k (neg-Fin k (neg-Fin k x))) ∙
    ( neg-neg-Fin k x))
```
