# Maximal structured natural numbers

```agda
module elementary-number-theory.maximal-structured-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.upper-bounds-natural-numbers

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.universe-levels
```

</details>

Consider a type family $P$ over $\mathbb{N}$. A {{#concept "maximal structured natural number" Agda=maximal-element-ℕ}} in $P$ is a natural number $n$ equipped with an element $p : P(n)$ such that $n$ is an [upper bound](elementary-number-theory.upper-bounds-natural-numbers.md) for $P$.

Forthermore, a {{#concept "bounded maximal structured natural number" Agda=bounded-maximal-element-ℕ}} in $P$ with bound $b$ is a natural number $n \leq b$ equipped with an element $p : P(n)$ such that $n$ is an upper bound of for the type family $x \mapsto (x \leq b) × P(x)$.

## Definitions

### The predicate of being a maximal structured natural number

```agda
is-maximal-element-ℕ :
  {l : Level} (P : ℕ → UU l) → ℕ → UU l
is-maximal-element-ℕ P n =
  P n × is-upper-bound-ℕ P n
```

### Maximal elements

```agda
maximal-element-ℕ :
  {l : Level} (P : ℕ → UU l) → UU l
maximal-element-ℕ P =
  Σ ℕ (is-maximal-element-ℕ P)

module _
  {l : Level} (P : ℕ → UU l) (n : maximal-element-ℕ P)
  where

  nat-maximal-element-ℕ : ℕ
  nat-maximal-element-ℕ = pr1 n

  structure-maximal-element-ℕ : P nat-maximal-element-ℕ
  structure-maximal-element-ℕ = pr1 (pr2 n)

  is-upper-bound-maximal-element-ℕ : is-upper-bound-ℕ P nat-maximal-element-ℕ
  is-upper-bound-maximal-element-ℕ = pr2 (pr2 n)

  is-least-upper-bound-maximal-element-ℕ :
    is-least-upper-bound-ℕ P nat-maximal-element-ℕ
  is-least-upper-bound-maximal-element-ℕ =
    is-least-upper-bound-is-upper-bound-ℕ P
      ( nat-maximal-element-ℕ)
      ( structure-maximal-element-ℕ)
      ( is-upper-bound-maximal-element-ℕ)
```

### The predicate of being a maximal bounded structured natural number

```agda
bounded-family-family-ℕ :
  {l : Level} (P : ℕ → UU l) → ℕ → ℕ → UU l
bounded-family-family-ℕ P b n = n ≤-ℕ b × P n

is-maximal-bounded-element-ℕ :
  {l : Level} (P : ℕ → UU l) → ℕ → ℕ → UU l
is-maximal-bounded-element-ℕ P b =
  is-maximal-element-ℕ (bounded-family-family-ℕ P b)
```

### Bounded maximal elements

```agda
bounded-maximal-element-ℕ :
  {l : Level} (P : ℕ → UU l) (b : ℕ) → UU l
bounded-maximal-element-ℕ P b =
  maximal-element-ℕ (bounded-family-family-ℕ P b)

module _
  {l : Level} (P : ℕ → UU l) (b : ℕ) (n : bounded-maximal-element-ℕ P b)
  where

  nat-bounded-maximal-element-ℕ : ℕ
  nat-bounded-maximal-element-ℕ = pr1 n

  upper-bound-bounded-maximal-element-ℕ : nat-bounded-maximal-element-ℕ ≤-ℕ b
  upper-bound-bounded-maximal-element-ℕ = pr1 (pr1 (pr2 n))

  structure-bounded-maximal-element-ℕ : P nat-bounded-maximal-element-ℕ
  structure-bounded-maximal-element-ℕ = pr2 (pr1 (pr2 n))

  is-upper-bound-bounded-maximal-element-ℕ :
    is-upper-bound-ℕ (bounded-family-family-ℕ P b) nat-bounded-maximal-element-ℕ
  is-upper-bound-bounded-maximal-element-ℕ = pr2 (pr2 n)

  is-least-upper-bound-bounded-maximal-element-ℕ :
    is-least-upper-bound-ℕ
      ( bounded-family-family-ℕ P b)
      ( nat-bounded-maximal-element-ℕ)
  is-least-upper-bound-bounded-maximal-element-ℕ =
    is-least-upper-bound-is-upper-bound-ℕ
      ( bounded-family-family-ℕ P b)
      ( nat-bounded-maximal-element-ℕ)
      ( upper-bound-bounded-maximal-element-ℕ ,
        structure-bounded-maximal-element-ℕ)
      ( is-upper-bound-bounded-maximal-element-ℕ)
```

