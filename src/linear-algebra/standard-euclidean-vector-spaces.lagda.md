# The standard Euclidean vector space

```agda
module linear-algebra.standard-euclidean-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

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
vector-space-ℝ^ : ℕ → (l : Level) → ℝ-Vector-Space l (lsuc l)
vector-space-ℝ^ n l =
  Π-left-module-Commutative-Ring
    ( commutative-ring-ℝ l)
    ( Fin n)
    ( λ _ →
      left-module-commutative-ring-Commutative-Ring (commutative-ring-ℝ l))

type-ℝ^ : ℕ → (l : Level) → UU (lsuc l)
type-ℝ^ n l = type-ℝ-Vector-Space (vector-space-ℝ^ n l)

add-ℝ^ : (n : ℕ) {l : Level} → type-ℝ^ n l → type-ℝ^ n l → type-ℝ^ n l
add-ℝ^ n {l} = add-ℝ-Vector-Space (vector-space-ℝ^ n l)

mul-ℝ^ : (n : ℕ) {l : Level} → ℝ l → type-ℝ^ n l → type-ℝ^ n l
mul-ℝ^ n {l} = mul-ℝ-Vector-Space (vector-space-ℝ^ n l)

zero-ℝ^ : (n : ℕ) (l : Level) → type-ℝ^ n l
zero-ℝ^ n l = zero-ℝ-Vector-Space (vector-space-ℝ^ n l)

neg-ℝ^ : (n : ℕ) {l : Level} → type-ℝ^ n l → type-ℝ^ n l
neg-ℝ^ n {l} = neg-ℝ-Vector-Space (vector-space-ℝ^ n l)

diff-ℝ^ : (n : ℕ) {l : Level} → type-ℝ^ n l → type-ℝ^ n l → type-ℝ^ n l
diff-ℝ^ n u v = add-ℝ^ n u (neg-ℝ^ n v)
```
