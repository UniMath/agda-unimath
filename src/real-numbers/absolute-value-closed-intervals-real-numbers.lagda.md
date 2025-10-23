# Absolute value on closed intervals in the real numbers

```agda
module real-numbers.absolute-value-closed-intervals-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import real-numbers.absolute-value-real-numbers
open import real-numbers.binary-maximum-real-numbers
open import real-numbers.closed-intervals-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.nonnegative-real-numbers
```

</details>

## Idea

The [absolute value](real-numbers.absolute-value-real-numbers.md) of an element
of a [closed interval](real-numbers.closed-intervals-real-numbers.md) `[a, b]`
of [real numbers](real-numbers.dedekind-real-numbers.md) is bounded by the
[maximum](real-numbers.binary-maximum-real-numbers.md).

## Definition

```agda
max-abs-closed-interval-ℝ :
  {l1 l2 : Level} → closed-interval-ℝ l1 l2 → ℝ (l1 ⊔ l2)
max-abs-closed-interval-ℝ ((a , b) , a≤b) = max-ℝ (neg-ℝ a) b
```

## Properties

### If `z ∈ [x, y]`, then `|z| ≤ max(|x|, |y|)`

```agda
abstract
  leq-max-abs-is-in-closed-interval-ℝ :
    {l1 l2 l3 : Level} ([x,y] : closed-interval-ℝ l1 l2) (z : ℝ l3) →
    is-in-closed-interval-ℝ [x,y] z →
    leq-ℝ (abs-ℝ z) (max-abs-closed-interval-ℝ [x,y])
  leq-max-abs-is-in-closed-interval-ℝ ((x , y) , x≤y) z (x≤z , z≤y) =
    leq-abs-leq-leq-neg-ℝ
      ( z)
      ( max-ℝ (neg-ℝ x) y)
      ( transitive-leq-ℝ _ _ _ (leq-right-max-ℝ _ _) z≤y)
      ( transitive-leq-ℝ _ _ _ (leq-left-max-ℝ _ _) (neg-leq-ℝ _ _ x≤z))
```

### The maximum absolute value of an interval is nonnegative

```agda
abstract
  is-nonnegative-max-abs-closed-interval-ℝ :
    {l1 l2 : Level} → ([a,b] : closed-interval-ℝ l1 l2) →
    is-nonnegative-ℝ (max-abs-closed-interval-ℝ [a,b])
  is-nonnegative-max-abs-closed-interval-ℝ [a,b]@((a , b) , a≤b) =
    is-nonnegative-leq-ℝ⁰⁺
      ( nonnegative-abs-ℝ a)
      ( max-ℝ (neg-ℝ a) b)
      ( leq-max-abs-is-in-closed-interval-ℝ [a,b] a (refl-leq-ℝ a , a≤b))

nonnegative-max-abs-closed-interval-ℝ :
  {l1 l2 : Level} → closed-interval-ℝ l1 l2 → ℝ⁰⁺ (l1 ⊔ l2)
nonnegative-max-abs-closed-interval-ℝ [a,b] =
  ( max-abs-closed-interval-ℝ [a,b] ,
    is-nonnegative-max-abs-closed-interval-ℝ [a,b])
```
