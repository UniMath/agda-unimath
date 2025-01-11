# Finite maps into the natural numbers

```agda
module elementary-number-theory.finite-maps-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.maximal-structured-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.propositions
open import foundation.universe-levels

open import univalent-combinatorics.finite-maps
```

</details>

## Idea

A map $f : A \to \mathbb{N}$ is said to be a {{#concept "finite map" Disambiguation="natural numbers"}} if its [fibers](foundation-core.finite-types.md) are [finite](univalent-combinatorics.finite-types.md).

Finite maps are [decidable](elementary-number-theory.decidable-maps-natural-numbers.md). Every finite map $f : \mathbb{N} \to \mathbb{N}$ has a definite lowest value, and for every finite map $f : \mathbb{N} \to \mathbb{N}$ that takes a value below $B$ there is a largest number $k$ such that $f(k) \leq b$.

The condition that $f : \mathbb{N} \to \mathbb{N}$ is finite is equivalent to the condition that for every natural number $n$, if $f$ has a value below $n$ there is a maximal number $k$ such that $f(k)\leq n$.

## Definitions

### The predicate of being a finite map into the natural numbers

```agda
module _
  {l : Level} {A : UU l} (f : A → ℕ)
  where

  is-finite-prop-map-ℕ : Prop l
  is-finite-prop-map-ℕ = is-finite-prop-map f
  
  is-finite-map-ℕ : UU l
  is-finite-map-ℕ = is-finite-map f

  is-prop-is-finite-map-ℕ : is-prop is-finite-map-ℕ
  is-prop-is-finite-map-ℕ = is-prop-is-finite-map f
```

### The maximal value-bound input property of a function on the natural numbers

The maximal value-bound input property asserts that for every natural number $n$ there is a maximal number $k$ for which $f(k)\leq n$. Note that it is not necessarily the case that the value $f(k)$ is itself maximal.

This property doesn't seem to have a widely recognized name, so we use an explicit descriptor.

```agda
maximal-value-bound-input-property-map-ℕ :
  (ℕ → ℕ) → UU lzero
maximal-value-bound-input-property-map-ℕ f =
  (n : ℕ) → maximal-element-ℕ (λ k → f k ≤-ℕ n)
```

## Properties

### Any finite map satisfies the maximal value-bound input property
