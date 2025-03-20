# An involution on the standard finite types

```agda
open import foundation.function-extensionality-axiom

module
  univalent-combinatorics.involution-standard-finite-types
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.modular-arithmetic-standard-finite-types funext
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.identity-types funext
open import foundation.involutions funext

open import univalent-combinatorics.standard-finite-types funext
```

</details>

## Idea

Every standard finite type `Fin k` has an involution operation given by
`x ↦ -x - 1`, using the group operations on `Fin k`.

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
  ( ( is-retraction-pred-Fin k (neg-Fin k (neg-Fin k x))) ∙
    ( neg-neg-Fin k x))
```
