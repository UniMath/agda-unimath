# Strictly inflationary functions on the natural numbers

```agda
module
  elementary-number-theory.strictly-inflationary-functions-natural-numbers
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.fibers-of-maps
open import foundation.universe-levels

open import order-theory.inflationary-maps-strictly-ordered-types
```

</details>

## Idea

A function $f : \mathbb{N} \to \mathbb{N}$ is a {{#concept "strictly inflationary function" Disambiguation="natural numbers" Agda=is-strictly-inflationary-ℕ}} if the implication

$$
  (x < y) \to (f(x) < f(y))
$$

holds for every $x,y:\mathbb{N}$. If $f$ is a strictly inflationary function on the natural numbers such that $f(0) \leq b$ for some natural number $b$, then there is a maximal natural number $k$ such that $f(k) \leq b$.

## Definitions

### The predicate of being a strictly inflationary map on the natural numbers

```agda
is-strictly-inflationary-ℕ : (ℕ → ℕ) → UU lzero
is-strictly-inflationary-ℕ =
  is-inflationary-map-Strictly-Ordered-Type ℕ-Strictly-Ordered-Type
```

### Strictly inflationary maps on the natural numbers

```agda
strictly-inflationary-map-ℕ : UU lzero
strictly-inflationary-map-ℕ =
  inflationary-map-Strictly-Ordered-Type ℕ-Strictly-Ordered-Type

map-strictly-inflationary-map-ℕ :
  strictly-inflationary-map-ℕ → ℕ → ℕ
map-strictly-inflationary-map-ℕ =
  map-inflationary-map-Strictly-Ordered-Type ℕ-Strictly-Ordered-Type

is-strictly-inflationary-strictly-inflationary-map-ℕ :
  (f : strictly-inflationary-map-ℕ) →
  is-strictly-inflationary-ℕ (map-strictly-inflationary-map-ℕ f)
is-strictly-inflationary-strictly-inflationary-map-ℕ =
  is-inflationary-inflationary-map-Strictly-Ordered-Type ℕ-Strictly-Ordered-Type

fiber-strictly-inflationary-map-ℕ :
  (f : strictly-inflationary-map-ℕ) → ℕ → UU lzero
fiber-strictly-inflationary-map-ℕ f = fiber (map-strictly-inflationary-map-ℕ f)
```

## Properties

### Strictly inflationary maps on the natural numbers are inflationary

```agda
is-inflationary-strictly-inflationary-map-ℕ :
  (f : strictly-inflationary-map-ℕ)
  (n : ℕ) → n ≤-ℕ map-strictly-inflationary-map-ℕ f n
is-inflationary-strictly-inflationary-map-ℕ f n =
  leq-le-ℕ n
    ( map-strictly-inflationary-map-ℕ f n)
    ( is-strictly-inflationary-strictly-inflationary-map-ℕ f n)
```

### Being a value of a strictly inflationary map is decidable

```agda
is-decidable-fiber-strictly-inflationary-map-ℕ :
  (f : strictly-inflationary-map-ℕ) →
  is-decidable-fam (fiber-strictly-inflationary-map-ℕ f)
is-decidable-fiber-strictly-inflationary-map-ℕ = {!!}
```

### For any strictly inflationary map $f$ with $f(0) \leq b$, there is a maximal number $k$ such that $f(k) \leq b$

