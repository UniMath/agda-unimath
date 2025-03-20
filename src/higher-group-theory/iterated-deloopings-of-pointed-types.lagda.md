# Iterated deloopings of pointed types

```agda
open import foundation.function-extensionality-axiom

module
  higher-group-theory.iterated-deloopings-of-pointed-types
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.cartesian-product-types funext
open import foundation.connected-types funext
open import foundation.dependent-pair-types
open import foundation.truncation-levels
open import foundation.universe-levels

open import structured-types.pointed-equivalences funext
open import structured-types.pointed-types

open import synthetic-homotopy-theory.iterated-loop-spaces funext
```

</details>

## Idea

The type of {{#concept "`n`-fold deloopings" Disambiguation="pointed type"}} of
a [pointed type](structured-types.pointed-types.md) `X` is the type

```text
  Σ (Y : Pointed-Type), is-connected (n-1) Y × (Ωⁿ X ≃∗ Y).
```

Here, the pointed type `Ωⁿ X` is the `n`-th
[iterated loop space](synthetic-homotopy-theory.iterated-loop-spaces.md) of `X`.

## Definitions

### The type of `n`-fold deloopings of a pointed type, with respect to a universe level

```agda
module _
  {l1 : Level} (l2 : Level) (n : ℕ) (X : Pointed-Type l1)
  where

  iterated-delooping-Level : UU (l1 ⊔ lsuc l2)
  iterated-delooping-Level =
    Σ ( Pointed-Type l2)
      ( λ Y →
        ( is-connected (truncation-level-minus-one-ℕ n) (type-Pointed-Type Y)) ×
        ( iterated-loop-space n X ≃∗ Y))
```

### The type of `n`-fold deloopings of a pointed type

```agda
module _
  {l1 : Level} (n : ℕ) (X : Pointed-Type l1)
  where

  iterated-delooping : UU (lsuc l1)
  iterated-delooping = iterated-delooping-Level l1 n X
```
