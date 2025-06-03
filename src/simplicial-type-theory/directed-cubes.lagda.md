# Directed cubes

```agda
module simplicial-type-theory.directed-cubes where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.negated-equality
open import foundation.negation
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.unit-type
open import foundation.universe-levels

open import simplicial-type-theory.directed-interval-type
open import simplicial-type-theory.inequality-directed-interval-type

open import synthetic-homotopy-theory.joins-of-types
```

</details>

## Idea

Given a [natural number](elementary-number-theory.natural-numbers.md) 𝑛, the
{{#concept "standard directed 𝑛-cube" Disambiguation="simplicial type theory" Agda=simplicial-cube}}
consists of 𝑛-fold pairs of elements of the
[directed interval](simplicial-type-theory.directed-interval-type.md). The
standard directed 0-cube is defined to be the
[unit type](foundation.unit-type.md).

## Definitions

### The standard directed cubes

```agda
simplicial-cube : ℕ → UU lzero
simplicial-cube 0 = unit
simplicial-cube 1 = Δ¹
simplicial-cube (succ-ℕ (succ-ℕ n)) = Δ¹ × simplicial-cube (succ-ℕ n)
```

### The standard left-associated directed cubes

```agda
left-associated-simplicial-cube : ℕ → UU lzero
left-associated-simplicial-cube 0 = unit
left-associated-simplicial-cube 1 = Δ¹
left-associated-simplicial-cube (succ-ℕ (succ-ℕ n)) =
  left-associated-simplicial-cube (succ-ℕ n) × Δ¹
```

### The standard directed power cubes

```agda
pow-simplicial-cube : ℕ → UU lzero
pow-simplicial-cube 0 = unit
pow-simplicial-cube 1 = Δ¹
pow-simplicial-cube (succ-ℕ (succ-ℕ n)) =
  pow-simplicial-cube (succ-ℕ n) × pow-simplicial-cube (succ-ℕ n)
```

### The boundary of the standard directed cube

```agda
subtype-boundary-simplicial-cube : (n : ℕ) → subtype lzero (simplicial-cube n)
subtype-boundary-simplicial-cube 0 _ =
  empty-Prop
subtype-boundary-simplicial-cube 1 x =
  join-Prop (Id-Δ¹-Prop x 0₂) (Id-Δ¹-Prop x 1₂)
subtype-boundary-simplicial-cube (succ-ℕ (succ-ℕ n)) (x , u) =
  join-Prop
    ( subtype-boundary-simplicial-cube 1 x)
    ( subtype-boundary-simplicial-cube (succ-ℕ n) u)

boundary-simplicial-cube : ℕ → UU lzero
boundary-simplicial-cube = type-subtype ∘ subtype-boundary-simplicial-cube
```

### The predicate of being an initial element in the simplicial 𝑛-cube

```agda
is-initial-element-simplicial-cube : (n : ℕ) → simplicial-cube n → UU lzero
is-initial-element-simplicial-cube 0 _ = unit
is-initial-element-simplicial-cube 1 x = (x ＝ 0₂)
is-initial-element-simplicial-cube (succ-ℕ (succ-ℕ n)) (x , y) =
  ( is-initial-element-simplicial-cube 1 x) ×
  ( is-initial-element-simplicial-cube (succ-ℕ n) y)

is-prop-is-initial-element-simplicial-cube :
  (n : ℕ) (x : simplicial-cube n) →
  is-prop (is-initial-element-simplicial-cube n x)
is-prop-is-initial-element-simplicial-cube 0 _ = is-prop-unit
is-prop-is-initial-element-simplicial-cube 1 x = is-set-Δ¹ x 0₂
is-prop-is-initial-element-simplicial-cube (succ-ℕ (succ-ℕ n)) (x , y) =
  is-prop-product
    ( is-prop-is-initial-element-simplicial-cube 1 x)
    ( is-prop-is-initial-element-simplicial-cube (succ-ℕ n) y)

is-initial-element-simplicial-cube-Prop :
  (n : ℕ) → simplicial-cube n → Prop lzero
is-initial-element-simplicial-cube-Prop n x =
  ( is-initial-element-simplicial-cube n x ,
    is-prop-is-initial-element-simplicial-cube n x)
```

### The predicate of being a terminal element in the simplicial 𝑛-cube

```agda
is-terminal-element-simplicial-cube : (n : ℕ) → simplicial-cube n → UU lzero
is-terminal-element-simplicial-cube 0 _ = unit
is-terminal-element-simplicial-cube 1 x = (x ＝ 1₂)
is-terminal-element-simplicial-cube (succ-ℕ (succ-ℕ n)) (x , y) =
  ( is-terminal-element-simplicial-cube 1 x) ×
  ( is-terminal-element-simplicial-cube (succ-ℕ n) y)

is-prop-is-terminal-element-simplicial-cube :
  (n : ℕ) (x : simplicial-cube n) →
  is-prop (is-terminal-element-simplicial-cube n x)
is-prop-is-terminal-element-simplicial-cube 0 _ = is-prop-unit
is-prop-is-terminal-element-simplicial-cube 1 x = is-set-Δ¹ x 1₂
is-prop-is-terminal-element-simplicial-cube (succ-ℕ (succ-ℕ n)) (x , y) =
  is-prop-product
    ( is-prop-is-terminal-element-simplicial-cube 1 x)
    ( is-prop-is-terminal-element-simplicial-cube (succ-ℕ n) y)

is-terminal-element-simplicial-cube-Prop :
  (n : ℕ) → simplicial-cube n → Prop lzero
is-terminal-element-simplicial-cube-Prop n x =
  ( is-terminal-element-simplicial-cube n x ,
    is-prop-is-terminal-element-simplicial-cube n x)
```

## Properties

### The simplicial 𝑛-cube is a set

```agda
is-set-simplicial-cube : (n : ℕ) → is-set (simplicial-cube n)
is-set-simplicial-cube zero-ℕ = is-set-unit
is-set-simplicial-cube (succ-ℕ zero-ℕ) = is-set-Δ¹
is-set-simplicial-cube (succ-ℕ (succ-ℕ n)) =
  is-set-product is-set-Δ¹ (is-set-simplicial-cube (succ-ℕ n))
```
