# Minimal structured natural numbers

```agda
module elementary-number-theory.minimal-structured-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.lower-bounds-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.universe-levels
```

</details>

## Idea

Consider a type family $P$ over $\mathbb{N}$. A {{#concept "minimal structured natural number" Agda=minimal-element-ℕ}} in $P$ is a natural number $n$ equipped with an element $p : P(n)$ such that $n$ is a [lower bound](elementary-number-theory.lower-bounds-natural-numbers.md) for $P$.

## Definitions

### The predicate of being a minimal structured natural number

```agda
is-minimal-element-ℕ :
  {l : Level} (P : ℕ → UU l) → ℕ → UU l
is-minimal-element-ℕ P n = P n × is-lower-bound-ℕ P n
```

### Minimal elements

```agda
minimal-element-ℕ :
  {l : Level} (P : ℕ → UU l) → UU l
minimal-element-ℕ P = Σ ℕ (is-minimal-element-ℕ P)

module _
  {l : Level} (P : ℕ → UU l) (n : minimal-element-ℕ P)
  where

  nat-minimal-element-ℕ : ℕ
  nat-minimal-element-ℕ = pr1 n

  structure-minimal-element-ℕ : P nat-minimal-element-ℕ
  structure-minimal-element-ℕ = pr1 (pr2 n)

  is-lower-bound-minimal-element-ℕ : is-lower-bound-ℕ P nat-minimal-element-ℕ
  is-lower-bound-minimal-element-ℕ = pr2 (pr2 n)

  is-largest-lower-bound-minimal-element-ℕ :
    is-largest-lower-bound-ℕ P nat-minimal-element-ℕ
  is-largest-lower-bound-minimal-element-ℕ =
    is-largest-lower-bound-is-lower-bound-ℕ P
      ( nat-minimal-element-ℕ)
      ( structure-minimal-element-ℕ)
      ( is-lower-bound-minimal-element-ℕ)
```

