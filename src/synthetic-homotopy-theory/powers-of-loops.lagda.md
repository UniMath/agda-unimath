# Powers of loops

```agda
open import foundation.function-extensionality-axiom

module
  synthetic-homotopy-theory.powers-of-loops
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.equivalences funext
open import foundation.identity-types funext
open import foundation.iterating-automorphisms funext
open import foundation.iterating-functions funext
open import foundation.universe-levels
open import foundation.whiskering-identifications-concatenation funext

open import structured-types.pointed-maps funext
open import structured-types.pointed-types

open import synthetic-homotopy-theory.functoriality-loop-spaces funext
open import synthetic-homotopy-theory.loop-spaces funext
```

</details>

## Idea

The **`n`-th power of a [loop](synthetic-homotopy-theory.loop-spaces.md)** `ω`
in a type `A` is defined by [iterated](foundation.iterating-functions.md)
[concatenation](foundation.identity-types.md) of `ω` with itself.

## Definitions

### Powers of loops by natural numbers

```agda
power-nat-Ω :
  {l : Level} → ℕ → (A : Pointed-Type l) → type-Ω A → type-Ω A
power-nat-Ω n A ω = iterate n (concat' (point-Pointed-Type A) ω) refl
```

### Powers of loops by integers

```agda
equiv-power-int-Ω :
  {l : Level} → ℤ → (A : Pointed-Type l) → type-Ω A → type-Ω A ≃ type-Ω A
equiv-power-int-Ω k A ω =
  iterate-automorphism-ℤ k (equiv-concat' (point-Pointed-Type A) ω)

power-int-Ω :
  {l : Level} → ℤ → (A : Pointed-Type l) → type-Ω A → type-Ω A
power-int-Ω k A ω = map-equiv (equiv-power-int-Ω k A ω) refl
```

## Properties

### `reflⁿ = refl`

```agda
power-nat-refl-Ω :
  {l : Level} (n : ℕ) (A : Pointed-Type l) →
  power-nat-Ω n A refl ＝ refl
power-nat-refl-Ω zero-ℕ A = refl
power-nat-refl-Ω (succ-ℕ n) A =
  right-whisker-concat (power-nat-refl-Ω n A) refl
```

### `ωⁿ⁺¹ = ωⁿ ∙ ω`

```agda
power-nat-succ-Ω :
  {l : Level} (n : ℕ) (A : Pointed-Type l) (ω : type-Ω A) →
  power-nat-Ω (succ-ℕ n) A ω ＝ (power-nat-Ω n A ω ∙ ω)
power-nat-succ-Ω n A ω = refl

power-nat-succ-Ω' :
  {l : Level} (n : ℕ) (A : Pointed-Type l) (ω : type-Ω A) →
  power-nat-Ω (succ-ℕ n) A ω ＝ (ω ∙ power-nat-Ω n A ω)
power-nat-succ-Ω' zero-ℕ A ω = inv right-unit
power-nat-succ-Ω' (succ-ℕ n) A ω =
  ( right-whisker-concat (power-nat-succ-Ω' n A ω) ω) ∙
  ( assoc ω (power-nat-Ω n A ω) ω)
```

### `ωᵐ⁺ⁿ ＝ ωᵐ ∙ ωⁿ`

```agda
power-nat-add-Ω :
  {l : Level} (m n : ℕ) (A : Pointed-Type l) (ω : type-Ω A) →
  power-nat-Ω (m +ℕ n) A ω ＝ (power-nat-Ω m A ω ∙ power-nat-Ω n A ω)
power-nat-add-Ω m zero-ℕ A ω = inv right-unit
power-nat-add-Ω m (succ-ℕ n) A ω =
  ( right-whisker-concat (power-nat-add-Ω m n A ω) ω) ∙
  ( assoc (power-nat-Ω m A ω) (power-nat-Ω n A ω) ω)
```

### `ωᵐⁿ = (ωᵐ)ⁿ`

```agda
power-nat-mul-Ω :
  {l : Level} (m n : ℕ) (A : Pointed-Type l) (ω : type-Ω A) →
  power-nat-Ω (m *ℕ n) A ω ＝ power-nat-Ω m A (power-nat-Ω n A ω)
power-nat-mul-Ω zero-ℕ n A ω = refl
power-nat-mul-Ω (succ-ℕ m) n A ω =
  ( power-nat-add-Ω (m *ℕ n) n A ω) ∙
  ( ( right-whisker-concat
      ( power-nat-mul-Ω m n A ω)
      ( power-nat-Ω n A ω)))

power-nat-mul-Ω' :
  {l : Level} (m n : ℕ) (A : Pointed-Type l) (ω : type-Ω A) →
  power-nat-Ω (m *ℕ n) A ω ＝ power-nat-Ω n A (power-nat-Ω m A ω)
power-nat-mul-Ω' m n A ω =
  ( ap (λ u → power-nat-Ω u A ω) (commutative-mul-ℕ m n)) ∙
  ( power-nat-mul-Ω n m A ω)
```

### The action on identifications of a function preserves powers

```agda
map-power-nat-Ω :
  {l1 l2 : Level} (n : ℕ) {A : Pointed-Type l1} {B : Pointed-Type l2}
  (f : A →∗ B) (ω : type-Ω A) →
  map-Ω f (power-nat-Ω n A ω) ＝ power-nat-Ω n B (map-Ω f ω)
map-power-nat-Ω zero-ℕ {A} {B} f ω = preserves-refl-map-Ω f
map-power-nat-Ω (succ-ℕ n) {A} {B} f ω =
  ( preserves-mul-map-Ω f) ∙
  ( right-whisker-concat (map-power-nat-Ω n f ω) (map-Ω f ω))
```
