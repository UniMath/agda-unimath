# The large ring of Dedekind real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.large-ring-of-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.large-commutative-rings

open import foundation.universe-levels

open import real-numbers.large-additive-group-of-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.rational-real-numbers

open import ring-theory.large-rings
```

</details>

## Idea

The [Dedekind real numbers](real-numbers.dedekind-real-numbers.md) form a
[large commutative ring](commutative-algebra.large-commutative-rings.md) under
[addition](real-numbers.addition-real-numbers.md) and
[multiplication](real-numbers.multiplication-real-numbers.md).

## Definition

```agda
large-ring-ℝ : Large-Ring lsuc _⊔_
large-ring-ℝ =
  make-Large-Ring
    ( large-ab-add-ℝ)
    ( mul-ℝ)
    ( preserves-sim-mul-ℝ)
    ( one-ℝ)
    ( associative-mul-ℝ)
    ( left-unit-law-mul-ℝ)
    ( right-unit-law-mul-ℝ)
    ( left-distributive-mul-add-ℝ)
    ( right-distributive-mul-add-ℝ)

large-commutative-ring-ℝ : Large-Commutative-Ring lsuc _⊔_
large-commutative-ring-ℝ =
  make-Large-Commutative-Ring
    ( large-ring-ℝ)
    ( commutative-mul-ℝ)
```

## Properties

### The small commutative ring of real numbers at a universe level

```agda
commutative-ring-ℝ : (l : Level) → Commutative-Ring (lsuc l)
commutative-ring-ℝ =
  commutative-ring-Large-Commutative-Ring large-commutative-ring-ℝ
```
