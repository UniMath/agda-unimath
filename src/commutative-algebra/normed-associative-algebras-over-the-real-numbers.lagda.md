# Normed associative algebras over the real numbers

```agda
module commutative-algebra.normed-associative-real-algebras where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.associative-algebras-commutative-rings
open import commutative-algebra.normed-real-algebras

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import linear-algebra.normed-real-vector-spaces

open import real-numbers.large-ring-of-real-numbers
open import real-numbers.multiplication-real-numbers
```

</details>

## Idea

A
{{#concept "normed associative algebra" Disambiguation="over ℝ" Agda=normed-associative-algebra-ℝ}}
over the [real numbers](real-numbers.dedekind-real-numbers.md) is a
[normed algebra over ℝ](commutative-algebra.normed-real-algebras.md) that is
[associative](commutative-algebra.associative-algebras-commutative-rings.md).

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

### The real numbers are a normed associative algebra over themselves

```agda
real-normed-associative-algebra-ℝ :
  (l : Level) → normed-associative-algebra-ℝ l (lsuc l)
real-normed-associative-algebra-ℝ l =
  ( real-normed-algebra-ℝ l , associative-mul-ℝ)
```

## See also

- [Real Banach algebras](functional-analysis.real-banach-algebras.md)
