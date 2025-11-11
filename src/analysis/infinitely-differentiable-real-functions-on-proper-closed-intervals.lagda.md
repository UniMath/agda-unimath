# Infinitely differentiable real functions on proper closed intervals of ℝ

```agda
{-# OPTIONS --lossy-unification --guardedness #-}
module analysis.infinitely-differentiable-real-functions-on-proper-closed-intervals where
```

<details><summary>Imports</summary>

```agda
open import analysis.derivatives-of-real-functions-on-proper-closed-intervals

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
open import real-numbers.proper-closed-intervals-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-real-numbers
```

</details>

## Idea

A function `f` from a
[proper closed interval](real-numbers.proper-closed-intervals-real-numbers.md)
is
{{#concept "infinitely differentiable" WD="smooth function" WDID=Q868473 Disambiguation="function from a proper closed interval of ℝ to ℝ" Agda=is-infinitely-differentiable-real-function-proper-closed-interval-ℝ}}
if it is
[differentiable](analysis.derivatives-of-real-functions-on-proper-closed-intervals.md)
and its derivative is infinitely differentiable.

## Definition

```agda
record
  is-infinitely-differentiable-real-function-proper-closed-interval-ℝ
    {l1 : Level} (l2 : Level)
    ([a,b] : proper-closed-interval-ℝ l1 l1)
    (f : type-proper-closed-interval-ℝ l1 [a,b] → ℝ (l1 ⊔ l2)) :
    UU (lsuc l1 ⊔ lsuc l2)
  where

  coinductive

  field
    is-differentiable-is-infinitely-differentiable-real-function-proper-closed-interval-ℝ :
      is-differentiable-real-function-proper-closed-interval-ℝ [a,b] f
    is-infinitely-differentiable-derivative-is-infinitely-differentiable-real-function-proper-closed-interval-ℝ :
      is-infinitely-differentiable-real-function-proper-closed-interval-ℝ
        ( l2)
        ( [a,b])
        ( pr1
          ( is-differentiable-is-infinitely-differentiable-real-function-proper-closed-interval-ℝ))

open is-infinitely-differentiable-real-function-proper-closed-interval-ℝ
```

## Properties

### The constant zero function is infinitely differentiable

```agda
module _
  {l1 : Level} (l2 : Level)
  ([a,b] : proper-closed-interval-ℝ l1 l1)
  where

  is-infinitely-differentiable-constant-zero-function-proper-closed-interval-ℝ :
    is-infinitely-differentiable-real-function-proper-closed-interval-ℝ
      ( l2)
      ( [a,b])
      ( λ _ → raise-ℝ (l1 ⊔ l2) zero-ℝ)
  is-differentiable-is-infinitely-differentiable-real-function-proper-closed-interval-ℝ
    is-infinitely-differentiable-constant-zero-function-proper-closed-interval-ℝ =
    ( ( λ _ → raise-ℝ (l1 ⊔ l2) zero-ℝ) ,
      derivative-constant-real-function-proper-closed-interval-ℝ
        ( [a,b])
        ( raise-ℝ (l1 ⊔ l2) zero-ℝ))
  is-infinitely-differentiable-derivative-is-infinitely-differentiable-real-function-proper-closed-interval-ℝ
    is-infinitely-differentiable-constant-zero-function-proper-closed-interval-ℝ =
    is-infinitely-differentiable-constant-zero-function-proper-closed-interval-ℝ
```

### Any constant function is infinitely differentiable

```agda
module _
  {l1 l2 : Level}
  ([a,b] : proper-closed-interval-ℝ l1 l1)
  (c : ℝ (l1 ⊔ l2))
  where

  is-infinitely-differentiable-constant-function-proper-closed-interval-ℝ :
    is-infinitely-differentiable-real-function-proper-closed-interval-ℝ
      ( l2)
      ( [a,b])
      ( λ _ → c)
  is-differentiable-is-infinitely-differentiable-real-function-proper-closed-interval-ℝ
    is-infinitely-differentiable-constant-function-proper-closed-interval-ℝ =
    ( ( λ _ → raise-ℝ (l1 ⊔ l2) zero-ℝ) ,
      derivative-constant-real-function-proper-closed-interval-ℝ [a,b] c)
  is-infinitely-differentiable-derivative-is-infinitely-differentiable-real-function-proper-closed-interval-ℝ
    is-infinitely-differentiable-constant-function-proper-closed-interval-ℝ =
    is-infinitely-differentiable-constant-zero-function-proper-closed-interval-ℝ
      ( l2)
      ( [a,b])
```

### The identity function is infinitely differentiable

```agda
module _
  {l1 : Level}
  ([a,b] : proper-closed-interval-ℝ l1 l1)
  where

  is-infinitely-differentiable-id-function-proper-closed-interval-ℝ :
    is-infinitely-differentiable-real-function-proper-closed-interval-ℝ
      ( l1)
      ( [a,b])
      ( pr1)
  is-differentiable-is-infinitely-differentiable-real-function-proper-closed-interval-ℝ
    is-infinitely-differentiable-id-function-proper-closed-interval-ℝ =
    ( ( λ _ → raise-ℝ l1 one-ℝ) ,
      derivative-id-real-function-proper-closed-interval-ℝ [a,b])
  is-infinitely-differentiable-derivative-is-infinitely-differentiable-real-function-proper-closed-interval-ℝ
    is-infinitely-differentiable-id-function-proper-closed-interval-ℝ =
    is-infinitely-differentiable-constant-function-proper-closed-interval-ℝ
      ( [a,b])
      ( raise-ℝ l1 one-ℝ)
```

### The sum of infinitely differentiable functions is infinitely differentiable

This has yet to be proved.
