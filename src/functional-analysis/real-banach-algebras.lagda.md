# Real Banach algebras

```agda
module functional-analysis.real-banach-algebras where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.normed-associative-real-algebras

open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import functional-analysis.real-banach-spaces
```

</details>

## Idea

A {{#concept "real Banach algebra" Agda=ℝ-Banach-Algebra}} is a
[normed associative algebra over ℝ](commutative-algebra.normed-associative-real-algebras.md)
for which the associated
[normed vector space](linear-algebra.normed-real-vector-spaces.md) is a
[Banach space](functional-analysis.real-banach-spaces.md).

## Definition

```agda
is-banach-prop-normed-associative-algebra-ℝ :
  {l1 l2 : Level} → normed-associative-algebra-ℝ l1 l2 → Prop (l1 ⊔ l2)
is-banach-prop-normed-associative-algebra-ℝ A =
  is-banach-prop-Normed-ℝ-Vector-Space
    ( normed-vector-space-normed-associative-algebra-ℝ A)

is-banach-normed-associative-algebra-ℝ :
  {l1 l2 : Level} → normed-associative-algebra-ℝ l1 l2 → UU (l1 ⊔ l2)
is-banach-normed-associative-algebra-ℝ A =
  type-Prop (is-banach-prop-normed-associative-algebra-ℝ A)

ℝ-Banach-Algebra : (l1 l2 : Level) → UU (lsuc (l1 ⊔ l2))
ℝ-Banach-Algebra l1 l2 =
  type-subtype (is-banach-prop-normed-associative-algebra-ℝ {l1} {l2})
```

## Properties

### The real numbers are a real Banach algebra over themselves

```agda
real-banach-algebra-ℝ : (l : Level) → ℝ-Banach-Algebra l (lsuc l)
real-banach-algebra-ℝ l =
  ( real-normed-associative-algebra-ℝ l ,
    is-banach-normed-real-vector-space-ℝ l)
```

## External links

- [Banach algebra](https://en.wikipedia.org/wiki/Banach_algebra) on Wikipedia
