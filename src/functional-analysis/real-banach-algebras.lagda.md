# Real Banach algebras

```agda
module functional-analysis.real-banach-algebras where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import functional-analysis.real-banach-spaces

open import linear-algebra.normed-associative-algebras-over-the-real-numbers
```

</details>

## Idea

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
