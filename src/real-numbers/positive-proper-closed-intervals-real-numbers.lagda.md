# Positive proper closed intervals in the real numbers

```agda
module real-numbers.positive-proper-closed-intervals-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import real-numbers.absolute-value-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.proper-closed-intervals-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.strict-inequality-real-numbers
```

</details>

## Idea

A [proper closed interval](real-numbers.proper-closed-intervals-real-numbers.md)
in the [real numbers](real-numbers.dedekind-real-numbers.md) is
{{#concept "positive" Disambiguation="proper closed interval in ℝ" Agda=is-positive-proper-closed-interval-ℝ}}
if all its elements are [positive](real-numbers.positive-real-numbers.md), or
equivalently, if its lower bound is positive.

```agda
is-positive-prop-proper-closed-interval-ℝ :
  {l1 l2 : Level} → proper-closed-interval-ℝ l1 l2 → Prop l1
is-positive-prop-proper-closed-interval-ℝ (a , _ , _) = is-positive-prop-ℝ a

is-positive-proper-closed-interval-ℝ :
  {l1 l2 : Level} → proper-closed-interval-ℝ l1 l2 → UU l1
is-positive-proper-closed-interval-ℝ (a , _ , _) = is-positive-ℝ a
```

## Properties

### The bounds of a positive closed interval are positive

```agda
positive-lower-bound-is-positive-proper-closed-interval-ℝ :
  {l1 l2 : Level} ([a,b] : proper-closed-interval-ℝ l1 l2) →
  is-positive-proper-closed-interval-ℝ [a,b] → ℝ⁺ l1
positive-lower-bound-is-positive-proper-closed-interval-ℝ (a , _ , _) 0<a =
  ( a , 0<a)

positive-upper-bound-is-positive-proper-closed-interval-ℝ :
  {l1 l2 : Level} ([a,b] : proper-closed-interval-ℝ l1 l2) →
  is-positive-proper-closed-interval-ℝ [a,b] → ℝ⁺ l2
positive-upper-bound-is-positive-proper-closed-interval-ℝ (a , b , a<b) 0<a =
  ( b , transitive-le-ℝ zero-ℝ a b a<b 0<a)
```

### Elements of a positive closed interval are positive

```agda
abstract
  is-positive-is-in-positive-proper-closed-interval-ℝ :
    {l1 l2 l3 : Level} ([a,b] : proper-closed-interval-ℝ l1 l2) →
    is-positive-proper-closed-interval-ℝ [a,b] →
    (x : ℝ l3) → is-in-proper-closed-interval-ℝ [a,b] x → is-positive-ℝ x
  is-positive-is-in-positive-proper-closed-interval-ℝ
    (a , _ , _) 0<a x (a≤x , _) =
    concatenate-le-leq-ℝ zero-ℝ a x 0<a a≤x

positive-real-type-is-positive-proper-closed-interval-ℝ :
  {l1 l2 l3 : Level} ([a,b] : proper-closed-interval-ℝ l1 l2) →
  is-positive-proper-closed-interval-ℝ [a,b] →
  type-proper-closed-interval-ℝ l3 [a,b] → ℝ⁺ l3
positive-real-type-is-positive-proper-closed-interval-ℝ [a,b] 0<a (x , a≤x≤b) =
  ( x , is-positive-is-in-positive-proper-closed-interval-ℝ [a,b] 0<a x a≤x≤b)
```

### The absolute value of elements of a positive closed interval is bounded by the upper bound

```agda
abstract
  upper-bound-abs-is-in-positive-proper-closed-interval-ℝ :
    {l1 l2 l3 : Level} ([a,b] : proper-closed-interval-ℝ l1 l2) →
    is-positive-proper-closed-interval-ℝ [a,b] →
    (x : ℝ l3) → is-in-proper-closed-interval-ℝ [a,b] x →
    leq-ℝ (abs-ℝ x) (upper-bound-proper-closed-interval-ℝ [a,b])
  upper-bound-abs-is-in-positive-proper-closed-interval-ℝ
    (a , b , a<b) 0<a x (a≤x , x≤b) =
    inv-tr
      ( λ y → leq-ℝ y b)
      ( abs-real-ℝ⁺ (x , concatenate-le-leq-ℝ zero-ℝ a x 0<a a≤x))
      ( x≤b)
```
