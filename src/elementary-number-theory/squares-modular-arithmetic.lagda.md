# Squares in ℤₚ

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module elementary-number-theory.squares-modular-arithmetic
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.modular-arithmetic funext univalence truncations
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.squares-integers funext univalence truncations

open import foundation.decidable-types funext univalence truncations
open import foundation.dependent-pair-types
open import foundation.identity-types funext
open import foundation.universe-levels

open import univalent-combinatorics.fibers-of-maps funext univalence truncations
```

</details>

## Definition

```agda
square-ℤ-Mod : (p : ℕ) → ℤ-Mod p → ℤ-Mod p
square-ℤ-Mod p a = mul-ℤ-Mod p a a

cube-ℤ-Mod : (p : ℕ) → ℤ-Mod p → ℤ-Mod p
cube-ℤ-Mod p k = mul-ℤ-Mod p (square-ℤ-Mod p k) k

is-square-ℤ-Mod : (p : ℕ) → ℤ-Mod p → UU lzero
is-square-ℤ-Mod 0 k = is-square-ℤ k
is-square-ℤ-Mod (succ-ℕ p) k =
  Σ (ℤ-Mod (succ-ℕ p)) (λ x → square-ℤ-Mod (succ-ℕ p) x ＝ k)

square-root-ℤ-Mod : {p : ℕ} → (k : ℤ-Mod p) → is-square-ℤ-Mod p k → ℤ-Mod p
square-root-ℤ-Mod {0} _ (root , _) = root
square-root-ℤ-Mod {succ-ℕ p} _ (root , _) = root
```

## Properties

### Squareness in ℤₚ is decidable

```agda
is-decidable-is-square-ℤ-Mod :
  (p : ℕ) (k : ℤ-Mod p) →
  is-decidable (is-square-ℤ-Mod p k)
is-decidable-is-square-ℤ-Mod 0 k = is-decidable-is-square-ℤ k
is-decidable-is-square-ℤ-Mod (succ-ℕ p) k =
  is-decidable-fiber-Fin {succ-ℕ p} {succ-ℕ p} (square-ℤ-Mod (succ-ℕ p)) k
```
