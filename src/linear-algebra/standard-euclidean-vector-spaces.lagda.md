# The standard Euclidean vector space

```agda
{-# OPTIONS --lossy-unification #-}

module linear-algebra.standard-euclidean-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.sets
open import foundation.universe-levels

open import linear-algebra.dependent-products-left-modules-commutative-rings
open import linear-algebra.left-modules-commutative-rings
open import linear-algebra.real-vector-spaces

open import real-numbers.dedekind-real-numbers
open import real-numbers.large-ring-of-real-numbers

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The {{#concept "standard Euclidean space" WDID=Q17295 WD="Euclidean space"}}
`ℝⁿ` is the [real vector space](linear-algebra.real-vector-spaces.md) of
[finite sequences](lists.finite-sequences.md) of
[real numbers](real-numbers.dedekind-real-numbers.md) of length `n`.

## Definition

```agda
vector-space-ℝ-Fin : ℕ → (l : Level) → ℝ-Vector-Space l (lsuc l)
vector-space-ℝ-Fin n l =
  Π-left-module-Commutative-Ring
    ( commutative-ring-ℝ l)
    ( Fin n)
    ( λ _ →
      left-module-commutative-ring-Commutative-Ring (commutative-ring-ℝ l))

set-ℝ-Fin : ℕ → (l : Level) → Set (lsuc l)
set-ℝ-Fin n l = set-ℝ-Vector-Space (vector-space-ℝ-Fin n l)

type-ℝ-Fin : ℕ → (l : Level) → UU (lsuc l)
type-ℝ-Fin n l = type-ℝ-Vector-Space (vector-space-ℝ-Fin n l)

add-ℝ-Fin :
  {n : ℕ} {l : Level} →
  type-ℝ-Fin n l → type-ℝ-Fin n l → type-ℝ-Fin n l
add-ℝ-Fin {n} {l} =
  add-ℝ-Vector-Space (vector-space-ℝ-Fin n l)

mul-ℝ-Fin :
  {n : ℕ} {l : Level} → ℝ l → type-ℝ-Fin n l → type-ℝ-Fin n l
mul-ℝ-Fin {n} {l} =
  mul-ℝ-Vector-Space (vector-space-ℝ-Fin n l)

zero-ℝ-Fin : (n : ℕ) (l : Level) → type-ℝ-Fin n l
zero-ℝ-Fin n l = zero-ℝ-Vector-Space (vector-space-ℝ-Fin n l)

neg-ℝ-Fin :
  {n : ℕ} {l : Level} → type-ℝ-Fin n l → type-ℝ-Fin n l
neg-ℝ-Fin {n} {l} =
  neg-ℝ-Vector-Space (vector-space-ℝ-Fin n l)

diff-ℝ-Fin :
  {n : ℕ} {l : Level} →
  type-ℝ-Fin n l → type-ℝ-Fin n l → type-ℝ-Fin n l
diff-ℝ-Fin u v = add-ℝ-Fin u (neg-ℝ-Fin v)
```
