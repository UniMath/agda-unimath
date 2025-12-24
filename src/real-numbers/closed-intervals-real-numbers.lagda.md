# Closed intervals in the real numbers

```agda
module real-numbers.closed-intervals-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.additive-group-of-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.closed-subsets-metric-spaces
open import metric-spaces.complete-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.short-functions-metric-spaces
open import metric-spaces.subspaces-metric-spaces

open import order-theory.closed-intervals-large-posets

open import real-numbers.binary-maximum-real-numbers
open import real-numbers.binary-minimum-real-numbers
open import real-numbers.cauchy-completeness-dedekind-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.short-function-binary-maximum-real-numbers
open import real-numbers.short-function-binary-minimum-real-numbers
open import real-numbers.similarity-real-numbers
```

</details>

## Idea

A {{#concept "closed interval" Disambiguation="in ℝ" Agda=closed-interval-ℝ}} in
the [real numbers](real-numbers.dedekind-real-numbers.md) is a
[closed interval](order-theory.closed-intervals-large-posets.md) in the
[large poset](order-theory.large-posets.md) of the
[real numbers](real-numbers.inequality-real-numbers.md).

## Definition

```agda
closed-interval-ℝ : (l1 l2 : Level) → UU (lsuc (l1 ⊔ l2))
closed-interval-ℝ l1 l2 = closed-interval-Large-Poset ℝ-Large-Poset l1 l2

is-in-closed-interval-prop-ℝ :
  {l1 l2 l3 : Level} → closed-interval-ℝ l1 l3 → ℝ l2 → Prop (l1 ⊔ l2 ⊔ l3)
is-in-closed-interval-prop-ℝ =
  is-in-closed-interval-prop-Large-Poset ℝ-Large-Poset

is-in-closed-interval-ℝ :
  {l1 l2 l3 : Level} → closed-interval-ℝ l1 l2 → ℝ l3 → UU (l1 ⊔ l2 ⊔ l3)
is-in-closed-interval-ℝ =
  is-in-closed-interval-Large-Poset ℝ-Large-Poset

subtype-closed-interval-ℝ :
  {l1 l2 : Level} (l : Level) → closed-interval-ℝ l1 l2 →
  subtype (l1 ⊔ l2 ⊔ l) (ℝ l)
subtype-closed-interval-ℝ = subtype-closed-interval-Large-Poset ℝ-Large-Poset

type-closed-interval-ℝ :
  {l1 l2 : Level} (l : Level) → closed-interval-ℝ l1 l2 → UU (l1 ⊔ l2 ⊔ lsuc l)
type-closed-interval-ℝ l [a,b] =
  type-subtype (subtype-closed-interval-ℝ l [a,b])

lower-bound-closed-interval-ℝ : {l1 l2 : Level} → closed-interval-ℝ l1 l2 → ℝ l1
lower-bound-closed-interval-ℝ =
  lower-bound-closed-interval-Large-Poset ℝ-Large-Poset

upper-bound-closed-interval-ℝ : {l1 l2 : Level} → closed-interval-ℝ l1 l2 → ℝ l2
upper-bound-closed-interval-ℝ =
  upper-bound-closed-interval-Large-Poset ℝ-Large-Poset
```

## Properties

### The unit interval on the real numbers

```agda
unit-closed-interval-ℝ : closed-interval-ℝ lzero lzero
unit-closed-interval-ℝ =
  ((zero-ℝ , one-ℝ) , preserves-leq-real-ℚ leq-zero-one-ℚ)
```

### Closed intervals in the real numbers are closed in the metric space of real numbers

```agda
abstract opaque
  unfolding leq-ℝ neighborhood-ℝ

  is-closed-subset-closed-interval-ℝ :
    {l1 l2 l3 : Level} → ([a,b] : closed-interval-ℝ l1 l2) →
    is-closed-subset-Metric-Space
      ( metric-space-ℝ l3)
      ( subtype-closed-interval-ℝ l3 [a,b])
  is-closed-subset-closed-interval-ℝ ((a , b) , a≤b) x H =
    ( ( λ q q<a →
        let open do-syntax-trunc-Prop (lower-cut-ℝ x q)
        in do
          (r , q<r , r<a) ← forward-implication (is-rounded-lower-cut-ℝ a q) q<a
          let ε⁺@(ε , _) = positive-diff-le-ℚ q<r
          (y , Nεxy , a≤y , _) ← H ε⁺
          pr1 Nεxy
            ( q)
            ( a≤y
              ( q +ℚ ε)
              ( inv-tr
                ( is-in-lower-cut-ℝ a)
                ( is-identity-right-conjugation-add-ℚ q r)
                ( r<a)))) ,
      ( λ q q<x →
        let open do-syntax-trunc-Prop (lower-cut-ℝ b q)
        in do
          (r , q<r , r<x) ← forward-implication (is-rounded-lower-cut-ℝ x q) q<x
          let ε⁺@(ε , _) = positive-diff-le-ℚ q<r
          (y , Nεxy , _ , y≤b) ← H ε⁺
          y≤b
            ( q)
            ( pr2 Nεxy
              ( q)
              ( inv-tr
                ( is-in-lower-cut-ℝ x)
                ( is-identity-right-conjugation-add-ℚ q r)
                ( r<x)))))
```

### The metric space associated with a closed interval in ℝ

```agda
closed-subset-closed-interval-ℝ :
  {l1 l2 : Level} (l : Level) → closed-interval-ℝ l1 l2 →
  closed-subset-Metric-Space (l1 ⊔ l2 ⊔ l) (metric-space-ℝ l)
closed-subset-closed-interval-ℝ l [a,b] =
  ( subtype-closed-interval-ℝ l [a,b] ,
    is-closed-subset-closed-interval-ℝ [a,b])

metric-space-closed-interval-ℝ :
  {l1 l2 : Level} (l : Level) → closed-interval-ℝ l1 l2 →
  Metric-Space (l1 ⊔ l2 ⊔ lsuc l) l
metric-space-closed-interval-ℝ l [a,b] =
  subspace-closed-subset-Metric-Space
    ( metric-space-ℝ l)
    ( closed-subset-closed-interval-ℝ l [a,b])

complete-metric-space-closed-interval-ℝ :
  {l1 l2 : Level} (l : Level) → closed-interval-ℝ l1 l2 →
  Complete-Metric-Space (l1 ⊔ l2 ⊔ lsuc l) l
complete-metric-space-closed-interval-ℝ l [a,b] =
  complete-closed-subspace-Complete-Metric-Space
    ( complete-metric-space-ℝ l)
    ( closed-subset-closed-interval-ℝ l [a,b])

metric-space-unit-closed-interval-ℝ :
  (l : Level) → Metric-Space (lsuc l) l
metric-space-unit-closed-interval-ℝ l =
  metric-space-closed-interval-ℝ l unit-closed-interval-ℝ

complete-metric-space-unit-interval-ℝ :
  (l : Level) → Complete-Metric-Space (lsuc l) l
complete-metric-space-unit-interval-ℝ l =
  complete-metric-space-closed-interval-ℝ l unit-closed-interval-ℝ
```

### The clamping function

```agda
clamp-closed-interval-ℝ :
  {l1 l2 l3 : Level} ([a,b] : closed-interval-ℝ l1 l2) → ℝ l3 →
  type-closed-interval-ℝ (l1 ⊔ l2 ⊔ l3) [a,b]
clamp-closed-interval-ℝ ((a , b) , a≤b) x =
  ( max-ℝ a (min-ℝ b x) ,
    leq-left-max-ℝ _ _ ,
    leq-max-leq-leq-ℝ _ _ _ a≤b (leq-left-min-ℝ b x))
```

### The clamping function is a short function

```agda
abstract
  is-short-clamp-closed-interval-ℝ :
    {l1 l2 l3 : Level} ([a,b] : closed-interval-ℝ l1 l2) →
    is-short-function-Metric-Space
      ( metric-space-ℝ l3)
      ( metric-space-closed-interval-ℝ (l1 ⊔ l2 ⊔ l3) [a,b])
      ( clamp-closed-interval-ℝ [a,b])
  is-short-clamp-closed-interval-ℝ [a,b]@((a , b) , a≤b) =
    is-short-comp-is-short-function-Metric-Space
      ( metric-space-ℝ _)
      ( metric-space-ℝ _)
      ( metric-space-ℝ _)
      ( max-ℝ a)
      ( min-ℝ b)
      ( is-short-function-left-max-ℝ a)
      ( is-short-function-left-min-ℝ b)

short-clamp-closed-interval-ℝ :
  {l1 l2 l3 : Level} ([a,b] : closed-interval-ℝ l1 l2) →
  short-function-Metric-Space
    ( metric-space-ℝ l3)
    ( metric-space-closed-interval-ℝ (l1 ⊔ l2 ⊔ l3) [a,b])
short-clamp-closed-interval-ℝ [a,b] =
  ( clamp-closed-interval-ℝ [a,b] , is-short-clamp-closed-interval-ℝ [a,b])
```

### If `x ≤ a`, clamping `x` into `[a, b]` gives `a`

```agda
abstract
  clamp-leq-lower-bound-closed-interval-ℝ :
    {l1 l2 l3 : Level} ([a,b] : closed-interval-ℝ l1 l2) (x : ℝ l3) →
    leq-ℝ x (lower-bound-closed-interval-ℝ [a,b]) →
    sim-ℝ
      ( pr1 (clamp-closed-interval-ℝ [a,b] x))
      ( lower-bound-closed-interval-ℝ [a,b])
  clamp-leq-lower-bound-closed-interval-ℝ ((a , b) , a≤b) x x≤a =
    similarity-reasoning-ℝ
      max-ℝ a (min-ℝ b x)
      ~ℝ max-ℝ a x
        by
          preserves-sim-right-max-ℝ _ _ _
            ( right-leq-left-min-ℝ (transitive-leq-ℝ x a b a≤b x≤a))
      ~ℝ a
        by right-leq-left-max-ℝ x≤a
```

### If `b ≤ x`, clamping `x` into `[a, b]` gives `b`

```agda
abstract
  clamp-leq-upper-bound-closed-interval-ℝ :
    {l1 l2 l3 : Level} ([a,b] : closed-interval-ℝ l1 l2) (x : ℝ l3) →
    leq-ℝ (upper-bound-closed-interval-ℝ [a,b]) x →
    sim-ℝ
      ( pr1 (clamp-closed-interval-ℝ [a,b] x))
      ( upper-bound-closed-interval-ℝ [a,b])
  clamp-leq-upper-bound-closed-interval-ℝ ((a , b) , a≤b) x b≤x =
    similarity-reasoning-ℝ
      max-ℝ a (min-ℝ b x)
      ~ℝ max-ℝ a b
        by preserves-sim-right-max-ℝ _ _ _ (left-leq-right-min-ℝ b≤x)
      ~ℝ b
        by left-leq-right-max-ℝ a≤b
```
