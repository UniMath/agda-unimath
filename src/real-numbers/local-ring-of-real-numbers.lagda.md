# The local ring of Dedekind real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.local-ring-of-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.local-commutative-rings

open import foundation.dependent-pair-types
open import foundation.functoriality-disjunction
open import foundation.universe-levels

open import real-numbers.addition-nonzero-real-numbers
open import real-numbers.addition-real-numbers
open import real-numbers.large-ring-of-real-numbers
open import real-numbers.multiplicative-inverses-nonzero-real-numbers
open import real-numbers.nonzero-real-numbers
```

</details>

## Idea

The [ring of real numbers](real-numbers.large-ring-of-real-numbers.md) is a
[local](commutative-algebra.local-commutative-rings.md)
[commutative ring](commutative-algebra.commutative-rings.md).

## Definition

```agda
is-local-commutative-ring-ℝ :
  (l : Level) → is-local-Commutative-Ring (commutative-ring-ℝ l)
is-local-commutative-ring-ℝ l x y is-invertible-x+y =
  map-disjunction
    ( is-invertible-is-nonzero-ℝ x)
    ( is-invertible-is-nonzero-ℝ y)
    ( is-nonzero-either-is-nonzero-add-ℝ
      ( x)
      ( y)
      ( is-nonzero-is-invertible-ℝ (x +ℝ y) is-invertible-x+y))

local-commutative-ring-ℝ : (l : Level) → Local-Commutative-Ring (lsuc l)
local-commutative-ring-ℝ l =
  ( commutative-ring-ℝ l , is-local-commutative-ring-ℝ l)
```
