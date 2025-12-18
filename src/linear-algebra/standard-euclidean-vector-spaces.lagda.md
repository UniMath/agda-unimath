# The standard Euclidean vector space

```agda
module linear-algebra.standard-euclidean-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import linear-algebra.real-vector-spaces
open import linear-algebra.dependent-products-left-modules-commutative-rings
open import elementary-number-theory.natural-numbers
open import univalent-combinatorics.standard-finite-types
open import foundation.universe-levels
open import real-numbers.large-ring-of-real-numbers
open import real-numbers.dedekind-real-numbers
open import linear-algebra.left-modules-commutative-rings
```

</details>

## Idea

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
```
