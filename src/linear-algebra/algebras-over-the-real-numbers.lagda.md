# Algebras over the real numbers

```agda
module linear-algebra.algebras-over-the-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import linear-algebra.algebras-heyting-fields
open import real-numbers.field-of-real-numbers
open import foundation.universe-levels
open import group-theory.abelian-groups
open import linear-algebra.real-vector-spaces
open import real-numbers.dedekind-real-numbers
open import foundation.sets
```

</details>

## Idea

An {{#concept "algebra" Disambiguation="over the real numbers" Agda=algebra-ℝ}}
over the [real numbers](real-numbers.dedekind-real-numbers.md) is an
[algebra](linear-algebra.algebra-heyting-fields.md) over the
[field of real numbers](real-numbers.field-of-real-numbers.md).

## Definition

```agda
algebra-ℝ : (l1 l2 : Level) → UU (lsuc (l1 ⊔ l2))
algebra-ℝ l1 l2 = algebra-Heyting-Field l2 (heyting-field-ℝ l1)
```

## Properties

```agda
module _
  {l1 l2 : Level}
  (A : algebra-ℝ l1 l2)
  where

  vector-space-algebra-ℝ : ℝ-Vector-Space l1 l2
  vector-space-algebra-ℝ =
    vector-space-algebra-Heyting-Field (heyting-field-ℝ l1) A

  ab-add-algebra-ℝ : Ab l2
  ab-add-algebra-ℝ = ab-ℝ-Vector-Space vector-space-algebra-ℝ

  set-algebra-ℝ : Set l2
  set-algebra-ℝ = set-Ab ab-add-algebra-ℝ

  type-algebra-ℝ : UU l2
  type-algebra-ℝ = type-Ab ab-add-algebra-ℝ

  mul-algebra-ℝ : type-algebra-ℝ → type-algebra-ℝ → type-algebra-ℝ
  mul-algebra-ℝ = mul-algebra-Heyting-Field (heyting-field-ℝ l1) A
```
