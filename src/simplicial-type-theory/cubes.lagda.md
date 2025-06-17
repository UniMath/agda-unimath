# Directed cubes

```agda
open import foundation.universe-levels
open import order-theory.nontrivial-bounded-total-orders

module
  simplicial-type-theory.cubes
  {I1 I2 : Level} (I : Nontrivial-Bounded-Total-Order I1 I2)
  where
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

open import simplicial-type-theory.directed-interval-type I
open import simplicial-type-theory.inequality-directed-interval-type I

open import synthetic-homotopy-theory.joins-of-types
```

</details>

## Idea

Given a [natural number](elementary-number-theory.natural-numbers.md) 𝑛, the
{{#concept "standard directed 𝑛-cube" Disambiguation="simplicial type theory" Agda=directed-cube}}
consists of 𝑛-fold pairs of elements of the
[directed interval](simplicial-type-theory.directed-interval-type.md). The
standard directed 0-cube is defined to be the
[unit type](foundation.unit-type.md).

## Definitions

### The standard directed cubes

```agda
directed-cube : ℕ → UU I1
directed-cube 0 = raise-unit I1
directed-cube 1 = Δ¹
directed-cube (succ-ℕ (succ-ℕ n)) = Δ¹ × directed-cube (succ-ℕ n)
```

### The standard left-associated directed cubes

```agda
left-associated-directed-cube : ℕ → UU I1
left-associated-directed-cube 0 = raise-unit I1
left-associated-directed-cube 1 = Δ¹
left-associated-directed-cube (succ-ℕ (succ-ℕ n)) =
  left-associated-directed-cube (succ-ℕ n) × Δ¹
```

### The standard directed power cubes

```agda
pow-directed-cube : ℕ → UU I1
pow-directed-cube 0 = raise-unit I1
pow-directed-cube 1 = Δ¹
pow-directed-cube (succ-ℕ (succ-ℕ n)) =
  pow-directed-cube (succ-ℕ n) × pow-directed-cube (succ-ℕ n)
```

### The boundary of the standard directed cube

```agda
subtype-boundary-directed-cube : (n : ℕ) → subtype I1 (directed-cube n)
subtype-boundary-directed-cube 0 _ =
  raise-empty-Prop I1
subtype-boundary-directed-cube 1 x =
  join-Prop (Id-Δ¹-Prop x 0▵) (Id-Δ¹-Prop x 1▵)
subtype-boundary-directed-cube (succ-ℕ (succ-ℕ n)) (x , u) =
  join-Prop
    ( subtype-boundary-directed-cube 1 x)
    ( subtype-boundary-directed-cube (succ-ℕ n) u)

boundary-directed-cube : ℕ → UU I1
boundary-directed-cube = type-subtype ∘ subtype-boundary-directed-cube
```

### The predicate of being an initial element in the directed 𝑛-cube

```agda
is-initial-element-directed-cube : (n : ℕ) → directed-cube n → UU I1
is-initial-element-directed-cube 0 _ = raise-unit I1
is-initial-element-directed-cube 1 x = (x ＝ 0▵)
is-initial-element-directed-cube (succ-ℕ (succ-ℕ n)) (x , y) =
  ( is-initial-element-directed-cube 1 x) ×
  ( is-initial-element-directed-cube (succ-ℕ n) y)

is-prop-is-initial-element-directed-cube :
  (n : ℕ) (x : directed-cube n) →
  is-prop (is-initial-element-directed-cube n x)
is-prop-is-initial-element-directed-cube 0 _ = is-prop-raise-unit
is-prop-is-initial-element-directed-cube 1 x = is-set-Δ¹ x 0▵
is-prop-is-initial-element-directed-cube (succ-ℕ (succ-ℕ n)) (x , y) =
  is-prop-product
    ( is-prop-is-initial-element-directed-cube 1 x)
    ( is-prop-is-initial-element-directed-cube (succ-ℕ n) y)

is-initial-element-directed-cube-Prop :
  (n : ℕ) → directed-cube n → Prop I1
is-initial-element-directed-cube-Prop n x =
  ( is-initial-element-directed-cube n x ,
    is-prop-is-initial-element-directed-cube n x)
```

### The predicate of being a terminal element in the directed 𝑛-cube

```agda
is-terminal-element-directed-cube : (n : ℕ) → directed-cube n → UU I1
is-terminal-element-directed-cube 0 _ = raise-unit I1
is-terminal-element-directed-cube 1 x = (x ＝ 1▵)
is-terminal-element-directed-cube (succ-ℕ (succ-ℕ n)) (x , y) =
  ( is-terminal-element-directed-cube 1 x) ×
  ( is-terminal-element-directed-cube (succ-ℕ n) y)

is-prop-is-terminal-element-directed-cube :
  (n : ℕ) (x : directed-cube n) →
  is-prop (is-terminal-element-directed-cube n x)
is-prop-is-terminal-element-directed-cube 0 _ = is-prop-raise-unit
is-prop-is-terminal-element-directed-cube 1 x = is-set-Δ¹ x 1▵
is-prop-is-terminal-element-directed-cube (succ-ℕ (succ-ℕ n)) (x , y) =
  is-prop-product
    ( is-prop-is-terminal-element-directed-cube 1 x)
    ( is-prop-is-terminal-element-directed-cube (succ-ℕ n) y)

is-terminal-element-directed-cube-Prop :
  (n : ℕ) → directed-cube n → Prop I1
is-terminal-element-directed-cube-Prop n x =
  ( is-terminal-element-directed-cube n x ,
    is-prop-is-terminal-element-directed-cube n x)
```

## Properties

### The directed 𝑛-cube is a set

```agda
is-set-directed-cube : (n : ℕ) → is-set (directed-cube n)
is-set-directed-cube zero-ℕ = is-set-raise-unit
is-set-directed-cube (succ-ℕ zero-ℕ) = is-set-Δ¹
is-set-directed-cube (succ-ℕ (succ-ℕ n)) =
  is-set-product is-set-Δ¹ (is-set-directed-cube (succ-ℕ n))
```
