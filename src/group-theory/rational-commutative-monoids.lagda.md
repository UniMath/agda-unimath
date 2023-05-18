# Rational commutative monoids

```agda
module group-theory.rational-commutative-monoids where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.equivalences
open import foundation.universe-levels

open import group-theory.commutative-monoids
open import group-theory.powers-of-elements-commutative-monoids
```

</details>

## Idea

A **rational commutative monoid** is a [commutative monoid](group-theory.commutative-monoids.md) `(M,0,+)` in which the map `x ↦ nx` is invertible for every natural number `n`.

Note: since we usually write commutative monoids multiplicatively, the condition that a commutative monoid is rational is that the map `x ↦ xⁿ` is invertible for every natural number `n`.

## Definition

### The predicate of being a rational commutative monoid

```agda
is-rational-Commutative-Monoid : {l : Level} → Commutative-Monoid l → UU l
is-rational-Commutative-Monoid M =
  (n : ℕ) → is-equiv (power-Commutative-Monoid M n)
```
