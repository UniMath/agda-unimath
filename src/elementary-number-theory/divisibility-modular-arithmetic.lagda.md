# Divisibility in modular arithmetic

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module elementary-number-theory.divisibility-modular-arithmetic
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.divisibility-integers funext univalence truncations
open import elementary-number-theory.divisibility-standard-finite-types funext univalence truncations
open import elementary-number-theory.modular-arithmetic funext univalence truncations
open import elementary-number-theory.natural-numbers

open import foundation.binary-relations funext univalence truncations
open import foundation.decidable-types funext univalence truncations
open import foundation.dependent-pair-types
open import foundation.identity-types funext
open import foundation.universe-levels

open import univalent-combinatorics.fibers-of-maps funext univalence truncations
```

</details>

## Idea

For two numbers `x` and `y` in `ℤ-Mod k`, we say that `x` divides `y` if there
is a number `u` in `ℤ-Mod k` such that `mul-ℤ-Mod k u x = y`.

## Definition

```agda
div-ℤ-Mod : (k : ℕ) → ℤ-Mod k → ℤ-Mod k → UU lzero
div-ℤ-Mod k x y = Σ (ℤ-Mod k) (λ u → mul-ℤ-Mod k u x ＝ y)
```

## Properties

### The divisibility relation is reflexive

```agda
refl-div-ℤ-Mod : {k : ℕ} (x : ℤ-Mod k) → div-ℤ-Mod k x x
refl-div-ℤ-Mod {ℕ.zero-ℕ} = refl-div-ℤ
refl-div-ℤ-Mod {ℕ.succ-ℕ k} = refl-div-Fin
```

### The divisibility relation is transitive

```agda
transitive-div-ℤ-Mod : {k : ℕ} → is-transitive (div-ℤ-Mod k)
transitive-div-ℤ-Mod {zero-ℕ} = transitive-div-ℤ
transitive-div-ℤ-Mod {succ-ℕ k} = transitive-div-Fin (succ-ℕ k)
```

### The divisibility relation is decidable

```agda
is-decidable-div-ℤ-Mod :
  (k : ℕ) (x y : ℤ-Mod k) → is-decidable (div-ℤ-Mod k x y)
is-decidable-div-ℤ-Mod zero-ℕ x y = is-decidable-div-ℤ x y
is-decidable-div-ℤ-Mod (succ-ℕ k) x y = is-decidable-fiber-Fin
  {succ-ℕ k} {succ-ℕ k} (mul-ℤ-Mod' (succ-ℕ k) x) y
```
