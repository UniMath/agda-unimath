# The W-type of natural numbers

```agda
module trees.w-type-of-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.booleans
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.unit-type
open import foundation.universal-property-empty-type
open import foundation.universe-levels

open import trees.w-types
```

</details>

## Idea

Since the type of [natural numbers](elementary-number-theory.natural-numbers.md)
is an initial [algebra](trees.algebras-polynomial-endofunctors.md) for the
[polynomial endofunctor](trees.polynomial-endofunctors.md)

```text
  X ↦ X + 𝟙,
```

there is an [equivalent](foundation-core.equivalences.md) definition of the
natural numbers as a [W-type](trees.w-types.md).

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
