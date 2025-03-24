# Iterated suspensions of pointed types

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module synthetic-homotopy-theory.iterated-suspensions-of-pointed-types
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.iterating-functions funext univalence truncations
open import foundation.universe-levels

open import structured-types.pointed-types

open import synthetic-homotopy-theory.suspensions-of-pointed-types funext univalence truncations
```

</details>

## Idea

Given a [pointed type](structured-types.pointed-types.md) `X` and a
[natural number](elementary-number-theory.natural-numbers.md) `n`, we can form
the **`n`-iterated suspension** of `X`.

## Definitions

### The iterated suspension of a pointed type

```agda
iterated-suspension-Pointed-Type :
  {l : Level} (n : ℕ) → Pointed-Type l → Pointed-Type l
iterated-suspension-Pointed-Type n = iterate n suspension-Pointed-Type
```
