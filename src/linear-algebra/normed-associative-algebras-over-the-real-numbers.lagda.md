# Normed associative algebras over the real numbers

```agda
module linear-algebra.normed-associative-algebras-over-the-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import linear-algebra.associative-algebras-commutative-rings
open import linear-algebra.normed-algebras-over-the-real-numbers
open import linear-algebra.normed-real-vector-spaces

open import real-numbers.large-ring-of-real-numbers
```

</details>

## Idea

## Definition

```agda
normed-associative-algebra-ℝ : (l1 l2 : Level) → UU (lsuc (l1 ⊔ l2))
normed-associative-algebra-ℝ l1 l2 =
  Σ ( normed-algebra-ℝ l1 l2)
    ( λ A →
      is-associative-algebra-Commutative-Ring
        ( commutative-ring-ℝ l1)
        ( algebra-normed-algebra-ℝ A))
```

## Properties

```agda
module _
  {l1 l2 : Level}
  (A : normed-associative-algebra-ℝ l1 l2)
  where

  normed-algebra-normed-associative-algebra-ℝ : normed-algebra-ℝ l1 l2
  normed-algebra-normed-associative-algebra-ℝ = pr1 A

  normed-vector-space-normed-associative-algebra-ℝ : Normed-ℝ-Vector-Space l1 l2
  normed-vector-space-normed-associative-algebra-ℝ =
    normed-vector-space-normed-algebra-ℝ
      ( normed-algebra-normed-associative-algebra-ℝ)
```
