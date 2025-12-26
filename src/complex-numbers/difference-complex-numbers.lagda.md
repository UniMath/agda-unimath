# The difference of complex numbers

```agda
module complex-numbers.difference-complex-numbers where
```

<details><summary>Imports</summary>

```agda
open import complex-numbers.addition-complex-numbers
open import complex-numbers.complex-numbers
open import complex-numbers.similarity-complex-numbers
open import complex-numbers.zero-complex-numbers

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import real-numbers.difference-real-numbers
```

</details>

## Idea

The
{{#concept "difference" Disambiguation="of two complex numbers" Agda=diff-ℂ}} of
two [complex numbers](complex-numbers.complex-numbers.md) `z` and `w` is the
result of [adding](complex-numbers.addition-complex-numbers.md) `z` and `-w`.

## Definition

```agda
diff-ℂ : {l1 l2 : Level} → ℂ l1 → ℂ l2 → ℂ (l1 ⊔ l2)
diff-ℂ (a +iℂ b) (c +iℂ d) = (a -ℝ c) +iℂ (b -ℝ d)

infixl 36 _-ℂ_
_-ℂ_ : {l1 l2 : Level} → ℂ l1 → ℂ l2 → ℂ (l1 ⊔ l2)
_-ℂ_ = diff-ℂ
```

## Properties

### `-(z - w) = w - z`

```agda
abstract
  distributive-neg-diff-ℂ :
    {l1 l2 : Level} (z : ℂ l1) (w : ℂ l2) → neg-ℂ (z -ℂ w) ＝ w -ℂ z
  distributive-neg-diff-ℂ (a +iℂ b) (c +iℂ d) =
    eq-ℂ (distributive-neg-diff-ℝ a c) (distributive-neg-diff-ℝ b d)
```

### `(x - y) + (y - z) = x - z`

```agda
abstract
  add-diff-ℂ :
    {l1 l2 l3 : Level} (x : ℂ l1) (y : ℂ l2) (z : ℂ l3) →
    sim-ℂ ((x -ℂ y) +ℂ (y -ℂ z)) (x -ℂ z)
  add-diff-ℂ (a +iℂ b) (c +iℂ d) (e +iℂ f) =
    ( add-diff-ℝ a c e , add-diff-ℝ b d f)
```

### If `z - w = 0`, `z = w`

```agda
abstract
  sim-is-zero-diff-ℂ :
    {l1 l2 : Level} (z : ℂ l1) (w : ℂ l2) → is-zero-ℂ (z -ℂ w) → sim-ℂ z w
  sim-is-zero-diff-ℂ (a +iℂ b) (c +iℂ d) (a-c~0 , b-d~0) =
    ( sim-is-zero-diff-ℝ a c a-c~0 , sim-is-zero-diff-ℝ b d b-d~0)
```
