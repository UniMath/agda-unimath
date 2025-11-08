# Proper closed intervals in the real numbers

```agda
module real-numbers.proper-closed-intervals-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import real-numbers.dedekind-real-numbers
open import real-numbers.strict-inequality-real-numbers
open import real-numbers.subsets-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.closed-intervals-real-numbers

open import metric-spaces.metric-spaces
open import foundation.subtypes
open import foundation.conjunction
open import foundation.universe-levels
open import metric-spaces.complete-metric-spaces
open import foundation.dependent-pair-types
open import metric-spaces.closed-subsets-metric-spaces
```

</details>

## Idea

A
{{#concept "proper closed interval" Disambiguation="in ℝ" Agda=proper-closed-interval-ℝ}}
in the [real numbers](real-numbers.dedekind-real-numbers.md) is a
[closed interval](real-numbers.closed-intervals-real-numbers.md) in which the
lower bound is
[strictly less than](real-numbers.strict-inequality-real-numbers.md) the upper
bound.

## Definition

```agda
proper-closed-interval-ℝ : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
proper-closed-interval-ℝ l1 l2 = Σ (ℝ l1) (λ x → Σ (ℝ l2) (λ y → le-ℝ x y))

closed-interval-proper-closed-interval-ℝ :
  {l1 l2 : Level} → proper-closed-interval-ℝ l1 l2 → closed-interval-ℝ l1 l2
closed-interval-proper-closed-interval-ℝ (a , b , a<b) =
  ((a , b) , leq-le-ℝ a<b)

lower-bound-proper-closed-interval-ℝ :
  {l1 l2 : Level} → proper-closed-interval-ℝ l1 l2 → ℝ l1
lower-bound-proper-closed-interval-ℝ (a , b , a<b) = a

upper-bound-proper-closed-interval-ℝ :
  {l1 l2 : Level} → proper-closed-interval-ℝ l1 l2 → ℝ l2
upper-bound-proper-closed-interval-ℝ (a , b , a<b) = b

subtype-proper-closed-interval-ℝ :
  {l1 l2 : Level} (l : Level) → proper-closed-interval-ℝ l1 l2 →
  subset-ℝ (l1 ⊔ l2 ⊔ l) l
subtype-proper-closed-interval-ℝ l (a , b , _) x =
  leq-prop-ℝ a x ∧ leq-prop-ℝ x b

type-proper-closed-interval-ℝ :
  {l1 l2 : Level} (l : Level) → proper-closed-interval-ℝ l1 l2 →
  UU (l1 ⊔ l2 ⊔ lsuc l)
type-proper-closed-interval-ℝ l [a,b] =
  type-subtype (subtype-proper-closed-interval-ℝ l [a,b])
```

## Properties

### The metric space associated with a proper closed interval

```agda
metric-space-proper-closed-interval-ℝ :
  {l1 l2 : Level} (l : Level) → proper-closed-interval-ℝ l1 l2 →
  Metric-Space (l1 ⊔ l2 ⊔ lsuc l) l
metric-space-proper-closed-interval-ℝ l [a,b] =
  metric-space-closed-interval-ℝ
    ( l)
    ( closed-interval-proper-closed-interval-ℝ [a,b])
```

### The metric space associated with a proper closed interval is closed

```agda
abstract
  is-closed-subset-proper-closed-interval-ℝ :
    {l1 l2 l3 : Level} ([a,b] : proper-closed-interval-ℝ l1 l2) →
    is-closed-subset-Metric-Space
      ( metric-space-ℝ l3)
      ( subtype-proper-closed-interval-ℝ l3 [a,b])
  is-closed-subset-proper-closed-interval-ℝ [a,b] =
    is-closed-subset-closed-interval-ℝ
      ( closed-interval-proper-closed-interval-ℝ [a,b])

closed-subset-proper-closed-interval-ℝ :
  {l1 l2 : Level} (l : Level) → proper-closed-interval-ℝ l1 l2 →
  closed-subset-Metric-Space (l1 ⊔ l2 ⊔ l) (metric-space-ℝ l)
closed-subset-proper-closed-interval-ℝ l [a,b] =
  closed-subset-closed-interval-ℝ
    ( l)
    ( closed-interval-proper-closed-interval-ℝ [a,b])
```

### The complete metric space associated with a proper closed interval

```agda
complete-metric-space-proper-closed-interval-ℝ :
  {l1 l2 : Level} (l : Level) → proper-closed-interval-ℝ l1 l2 →
  Complete-Metric-Space (l1 ⊔ l2 ⊔ lsuc l) l
complete-metric-space-proper-closed-interval-ℝ l [a,b] =
  complete-metric-space-closed-interval-ℝ
    ( l)
    ( closed-interval-proper-closed-interval-ℝ [a,b])
```
