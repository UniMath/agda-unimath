# The W-type of natural numbers

```agda
module trees.w-type-of-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.booleans
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.functions
open import foundation.homotopies
open import foundation.identity-types
open import foundation.unit-type
open import foundation.universal-property-empty-type
open import foundation.universe-levels

open import trees.w-types
```

</details>

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

issec-ℕ-Nat-𝕎 : (Nat-𝕎-ℕ ∘ ℕ-Nat-𝕎) ~ id
issec-ℕ-Nat-𝕎 (tree-𝕎 true α) =
  ap ( tree-𝕎 true)
     ( eq-htpy H)
  where
  H : (z : unit) → Nat-𝕎-ℕ (ℕ-Nat-𝕎 (α star)) ＝ α z
  H star = issec-ℕ-Nat-𝕎 (α star)
issec-ℕ-Nat-𝕎 (tree-𝕎 false α) =
  ap (tree-𝕎 false) (eq-is-contr (universal-property-empty' Nat-𝕎))

isretr-ℕ-Nat-𝕎 : (ℕ-Nat-𝕎 ∘ Nat-𝕎-ℕ) ~ id
isretr-ℕ-Nat-𝕎 zero-ℕ = refl
isretr-ℕ-Nat-𝕎 (succ-ℕ x) = ap succ-ℕ (isretr-ℕ-Nat-𝕎 x)

is-equiv-Nat-𝕎-ℕ : is-equiv Nat-𝕎-ℕ
is-equiv-Nat-𝕎-ℕ =
  is-equiv-has-inverse
    ℕ-Nat-𝕎
    issec-ℕ-Nat-𝕎
    isretr-ℕ-Nat-𝕎

equiv-Nat-𝕎-ℕ : ℕ ≃ Nat-𝕎
equiv-Nat-𝕎-ℕ = pair Nat-𝕎-ℕ is-equiv-Nat-𝕎-ℕ

is-equiv-ℕ-Nat-𝕎 : is-equiv ℕ-Nat-𝕎
is-equiv-ℕ-Nat-𝕎 =
  is-equiv-has-inverse
    Nat-𝕎-ℕ
    isretr-ℕ-Nat-𝕎
    issec-ℕ-Nat-𝕎

equiv-ℕ-Nat-𝕎 : Nat-𝕎 ≃ ℕ
equiv-ℕ-Nat-𝕎 = pair ℕ-Nat-𝕎 is-equiv-ℕ-Nat-𝕎
```
