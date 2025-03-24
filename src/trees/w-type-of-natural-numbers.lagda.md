# The W-type of natural numbers

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module trees.w-type-of-natural-numbers
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.booleans funext univalence truncations
open import foundation.contractible-types funext univalence
open import foundation.dependent-pair-types
open import foundation.dependent-products-contractible-types funext
open import foundation.equivalences funext
open import foundation.function-extensionality funext
open import foundation.function-types funext
open import foundation.homotopies funext
open import foundation.identity-types funext
open import foundation.unit-type
open import foundation.universal-property-empty-type funext
open import foundation.universe-levels

open import trees.w-types funext univalence truncations
```

</details>

## Idea

Since the type of natural numbers is an initial algebra for the polynomial
endofunctor

```text
  X ↦ X + 𝟙,
```

there is an equivalent definition of the natural numbers as a W-type.

## Definition

### The type of natural numbers defined as a W-type

```agda
Nat-𝕎 : UU lzero
Nat-𝕎 = 𝕎 bool (Eq-bool true)

zero-Nat-𝕎 : Nat-𝕎
zero-Nat-𝕎 = constant-𝕎 false id

succ-Nat-𝕎 : Nat-𝕎 → Nat-𝕎
succ-Nat-𝕎 x = tree-𝕎 true (λ y → x)
```

## Properties

### The type of natural numbers is equivalent to the W-type Nat-𝕎

```agda
Nat-𝕎-ℕ : ℕ → Nat-𝕎
Nat-𝕎-ℕ zero-ℕ = zero-Nat-𝕎
Nat-𝕎-ℕ (succ-ℕ x) = succ-Nat-𝕎 (Nat-𝕎-ℕ x)

ℕ-Nat-𝕎 : Nat-𝕎 → ℕ
ℕ-Nat-𝕎 (tree-𝕎 true α) = succ-ℕ (ℕ-Nat-𝕎 (α star))
ℕ-Nat-𝕎 (tree-𝕎 false α) = zero-ℕ

is-section-ℕ-Nat-𝕎 : (Nat-𝕎-ℕ ∘ ℕ-Nat-𝕎) ~ id
is-section-ℕ-Nat-𝕎 (tree-𝕎 true α) =
  ap
    ( tree-𝕎 true)
    ( eq-htpy H)
  where
  H : (z : unit) → Nat-𝕎-ℕ (ℕ-Nat-𝕎 (α star)) ＝ α z
  H star = is-section-ℕ-Nat-𝕎 (α star)
is-section-ℕ-Nat-𝕎 (tree-𝕎 false α) =
  ap (tree-𝕎 false) (eq-is-contr (universal-property-empty' Nat-𝕎))

is-retraction-ℕ-Nat-𝕎 : (ℕ-Nat-𝕎 ∘ Nat-𝕎-ℕ) ~ id
is-retraction-ℕ-Nat-𝕎 zero-ℕ = refl
is-retraction-ℕ-Nat-𝕎 (succ-ℕ x) = ap succ-ℕ (is-retraction-ℕ-Nat-𝕎 x)

is-equiv-Nat-𝕎-ℕ : is-equiv Nat-𝕎-ℕ
is-equiv-Nat-𝕎-ℕ =
  is-equiv-is-invertible
    ℕ-Nat-𝕎
    is-section-ℕ-Nat-𝕎
    is-retraction-ℕ-Nat-𝕎

equiv-Nat-𝕎-ℕ : ℕ ≃ Nat-𝕎
equiv-Nat-𝕎-ℕ = pair Nat-𝕎-ℕ is-equiv-Nat-𝕎-ℕ

is-equiv-ℕ-Nat-𝕎 : is-equiv ℕ-Nat-𝕎
is-equiv-ℕ-Nat-𝕎 =
  is-equiv-is-invertible
    Nat-𝕎-ℕ
    is-retraction-ℕ-Nat-𝕎
    is-section-ℕ-Nat-𝕎

equiv-ℕ-Nat-𝕎 : Nat-𝕎 ≃ ℕ
equiv-ℕ-Nat-𝕎 = pair ℕ-Nat-𝕎 is-equiv-ℕ-Nat-𝕎
```
