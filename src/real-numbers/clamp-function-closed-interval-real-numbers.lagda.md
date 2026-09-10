# The clamp function into closed interval in the real numbers

```agda
module real-numbers.clamp-function-closed-interval-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.closed-subsets-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.short-maps-metric-spaces
open import metric-spaces.subspaces-metric-spaces

open import real-numbers.binary-maximum-real-numbers
open import real-numbers.binary-minimum-real-numbers
open import real-numbers.closed-intervals-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.short-map-binary-maximum-real-numbers
open import real-numbers.short-map-binary-minimum-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.strict-inequality-real-numbers
```

</details>

## Idea

The
{{#concept "clamp function" Disambiguation="on a closed interval of real numbers" Agda=clamp-closed-interval-ℝ}}
on a [closed interval](real-numbers.closed-intervals-real-numbers.md) of
[real numbers](real-numbers.dedekind-real-numbers.md) `[a, b]` is the function

```text
  clamp-[a,b] : ℝ → [a, b]
  clamp-[a,b] = max a ∘ min b
```

For any `x ∈ ℝ`,

- if `x ≤ a` then `clamp-[a,b] x ＝ a`;
- if `b ≤ x` then `clamp-[a,b] x ＝ b`;
- if `a ≤ x ≤ b` then `clamp-[a,b] x ＝ x`.

In particular, the **clamp function** is
[idempotent](foundation.idempotent-maps.md).

## Definition

### The clamping function

```agda
module _
  {l1 l2 l3 : Level}
  ([a,b]@((a , b) , a≤b) : closed-interval-ℝ l1 l2)
  (x : ℝ l3)
  where

  map-clamp-closed-interval-ℝ : ℝ (l1 ⊔ l2 ⊔ l3)
  map-clamp-closed-interval-ℝ = max-ℝ a (min-ℝ b x)

  abstract
    leq-lower-bound-map-clamp-closed-interval-ℝ :
      leq-ℝ a map-clamp-closed-interval-ℝ
    leq-lower-bound-map-clamp-closed-interval-ℝ =
      leq-left-max-ℝ _ _

    leq-upper-bound-map-clamp-closed-interval-ℝ :
      leq-ℝ map-clamp-closed-interval-ℝ b
    leq-upper-bound-map-clamp-closed-interval-ℝ =
      leq-max-leq-leq-ℝ _ _ _ a≤b (leq-left-min-ℝ b x)

    is-in-closed-interval-map-clamp-closed-interval-ℝ :
      is-in-closed-interval-ℝ [a,b] map-clamp-closed-interval-ℝ
    is-in-closed-interval-map-clamp-closed-interval-ℝ =
      ( leq-lower-bound-map-clamp-closed-interval-ℝ ,
        leq-upper-bound-map-clamp-closed-interval-ℝ)

  clamp-closed-interval-ℝ : type-closed-interval-ℝ (l1 ⊔ l2 ⊔ l3) [a,b]
  clamp-closed-interval-ℝ =
    ( map-clamp-closed-interval-ℝ ,
      is-in-closed-interval-map-clamp-closed-interval-ℝ)
```

### The clamping function is a short map

```agda
abstract
  is-short-map-clamp-closed-interval-ℝ :
    {l1 l2 l3 : Level} ([a,b] : closed-interval-ℝ l1 l2) →
    is-short-map-Metric-Space
      ( metric-space-ℝ l3)
      ( metric-space-closed-interval-ℝ (l1 ⊔ l2 ⊔ l3) [a,b])
      ( clamp-closed-interval-ℝ [a,b])
  is-short-map-clamp-closed-interval-ℝ [a,b]@((a , b) , a≤b) =
    is-short-map-comp-Metric-Space
      ( metric-space-ℝ _)
      ( metric-space-ℝ _)
      ( metric-space-ℝ _)
      ( max-ℝ a)
      ( min-ℝ b)
      ( is-short-map-left-max-ℝ a)
      ( is-short-map-left-min-ℝ b)

short-map-clamp-closed-interval-ℝ :
  {l1 l2 l3 : Level} ([a,b] : closed-interval-ℝ l1 l2) →
  short-map-Metric-Space
    ( metric-space-ℝ l3)
    ( metric-space-closed-interval-ℝ (l1 ⊔ l2 ⊔ l3) [a,b])
short-map-clamp-closed-interval-ℝ [a,b] =
  ( clamp-closed-interval-ℝ [a,b] , is-short-map-clamp-closed-interval-ℝ [a,b])
```

### If `x ≤ a`, clamping `x` into `[a, b]` gives `a`

```agda
abstract
  sim-clamp-leq-lower-bound-closed-interval-ℝ :
    {l1 l2 l3 : Level} ([a,b] : closed-interval-ℝ l1 l2) (x : ℝ l3) →
    leq-ℝ x (lower-bound-closed-interval-ℝ [a,b]) →
    sim-ℝ
      ( map-clamp-closed-interval-ℝ [a,b] x)
      ( lower-bound-closed-interval-ℝ [a,b])
  sim-clamp-leq-lower-bound-closed-interval-ℝ ((a , b) , a≤b) x x≤a =
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
  sim-clamp-leq-upper-bound-closed-interval-ℝ :
    {l1 l2 l3 : Level} ([a,b] : closed-interval-ℝ l1 l2) (x : ℝ l3) →
    leq-ℝ (upper-bound-closed-interval-ℝ [a,b]) x →
    sim-ℝ
      ( map-clamp-closed-interval-ℝ [a,b] x)
      ( upper-bound-closed-interval-ℝ [a,b])
  sim-clamp-leq-upper-bound-closed-interval-ℝ ((a , b) , a≤b) x b≤x =
    similarity-reasoning-ℝ
      max-ℝ a (min-ℝ b x)
      ~ℝ max-ℝ a b
        by preserves-sim-right-max-ℝ _ _ _ (left-leq-right-min-ℝ b≤x)
      ~ℝ b
        by left-leq-right-max-ℝ a≤b
```

### If `x ∈ [a, b]` then clamping `x` into `[a, b]` gives `x`

```agda
abstract
  sim-clamp-is-in-closed-interval-ℝ :
    {l1 l2 l3 : Level} ([a,b] : closed-interval-ℝ l1 l2) (x : ℝ l3) →
    is-in-closed-interval-ℝ [a,b] x →
    sim-ℝ
      ( map-clamp-closed-interval-ℝ [a,b] x)
      ( x)
  sim-clamp-is-in-closed-interval-ℝ ((a , b) , a≤b) x (a≤x , x≤b) =
    similarity-reasoning-ℝ
      max-ℝ a (min-ℝ b x)
      ~ℝ max-ℝ a x
        by preserves-sim-right-max-ℝ _ _ _ (right-leq-left-min-ℝ x≤b)
      ~ℝ x
        by left-leq-right-max-ℝ a≤x

  compute-clamp-in-closed-interval-ℝ :
    {l l1 l2 : Level} (I : closed-interval-ℝ l1 l2)
    (x : type-closed-interval-ℝ (l ⊔ l1 ⊔ l2) I) →
    clamp-closed-interval-ℝ I (pr1 x) ＝ x
  compute-clamp-in-closed-interval-ℝ I (x , x∈I) =
    eq-type-subtype
      ( subtype-closed-interval-ℝ _ I)
      ( eq-sim-ℝ
        ( sim-clamp-is-in-closed-interval-ℝ I x x∈I))
```

### The clamping function is idempotent

```agda
abstract
  is-idempotent-map-clamp-closed-interval-ℝ :
    {l1 l2 l3 : Level} ([a,b] : closed-interval-ℝ l1 l2) (x : ℝ l3) →
    map-clamp-closed-interval-ℝ [a,b] (map-clamp-closed-interval-ℝ [a,b] x) ＝
    map-clamp-closed-interval-ℝ [a,b] x
  is-idempotent-map-clamp-closed-interval-ℝ [a,b] x =
    eq-sim-ℝ
      ( sim-clamp-is-in-closed-interval-ℝ
        ( [a,b])
        ( map-clamp-closed-interval-ℝ [a,b] x)
        ( is-in-closed-interval-map-clamp-closed-interval-ℝ [a,b] x))
```

### The clamping function is increasing

```agda
abstract
  is-increasing-map-clamp-closed-interval-ℝ :
      {l1 l2 l3 l4 : Level} (I : closed-interval-ℝ l1 l2)
      (x : ℝ l3)
      (y : ℝ l4) →
      leq-ℝ x y →
      leq-ℝ
        ( map-clamp-closed-interval-ℝ I x)
        ( map-clamp-closed-interval-ℝ I y)
  is-increasing-map-clamp-closed-interval-ℝ I x y =
    is-increasing-max-ℝ
      ( lower-bound-closed-interval-ℝ I)
      ( min-ℝ (upper-bound-closed-interval-ℝ I) x)
      ( min-ℝ (upper-bound-closed-interval-ℝ I) y) ∘
    is-increasing-min-ℝ
      ( upper-bound-closed-interval-ℝ I)
      ( x)
      ( y)
```

### For any `x y ∈ I`, if `x < y` then `clamp-I x < clamp-I y `

```agda
abstract
  le-map-clamp-le-is-in-closed-interval-ℝ :
    {l1 l2 l3 l4 : Level} (I : closed-interval-ℝ l1 l2) →
    (x : ℝ l3) (Hx : is-in-closed-interval-ℝ I x) →
    (y : ℝ l4) (Hy : is-in-closed-interval-ℝ I y) →
    le-ℝ x y →
    le-ℝ
      ( map-clamp-closed-interval-ℝ I x)
      ( map-clamp-closed-interval-ℝ I y)
  le-map-clamp-le-is-in-closed-interval-ℝ I x Hx y Hy =
    preserves-le-sim-ℝ
      ( symmetric-sim-ℝ
        ( sim-clamp-is-in-closed-interval-ℝ I x Hx))
      ( symmetric-sim-ℝ
        ( sim-clamp-is-in-closed-interval-ℝ I y Hy))
```

### The clamp function preserves similarity

```agda
sim-clamp-closed-interval-ℝ :
    {l1 l2 l3 l4 : Level} (I : closed-interval-ℝ l1 l2) →
    (x : ℝ l3) →
    (y : ℝ l4) →
    sim-ℝ x y →
    sim-ℝ
      ( map-clamp-closed-interval-ℝ I x)
      ( map-clamp-closed-interval-ℝ I y)
sim-clamp-closed-interval-ℝ I x y x~y =
  sim-antisymmetric-leq-ℝ
    ( map-clamp-closed-interval-ℝ I x)
    ( map-clamp-closed-interval-ℝ I y)
    ( is-increasing-map-clamp-closed-interval-ℝ I x y
      ( leq-sim-ℝ x~y))
    ( is-increasing-map-clamp-closed-interval-ℝ I y x
      ( leq-sim-ℝ' x~y))
```
