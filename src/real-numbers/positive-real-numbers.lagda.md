# Positive real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.positive-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.additive-group-of-rational-numbers
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.groups

open import real-numbers.addition-real-numbers
open import real-numbers.arithmetically-located-dedekind-cuts
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.strict-inequality-real-numbers
```

</details>

## Idea

A [real number](real-numbers.dedekind-real-numbers.md) is **positive** if zero
is [strictly less than](real-numbers.strict-inequality-real-numbers.md) it.

## Definition

```agda
is-positive-prop-ℝ : {l : Level} → ℝ l → Prop l
is-positive-prop-ℝ = le-ℝ-Prop zero-ℝ

is-positive-ℝ : {l : Level} → ℝ l → UU l
is-positive-ℝ x = type-Prop (is-positive-prop-ℝ x)

subtype-positive-ℝ : (l : Level) → subtype l (ℝ l)
subtype-positive-ℝ l = is-positive-prop-ℝ {l}

ℝ⁺ : (l : Level) → UU (lsuc l)
ℝ⁺ l = type-subtype (subtype-positive-ℝ l)

real-ℝ⁺ : {l : Level} → ℝ⁺ l → ℝ l
real-ℝ⁺ = pr1

is-positive-real-ℝ⁺ : {l : Level} → (x : ℝ⁺ l) → is-positive-ℝ (real-ℝ⁺ x)
is-positive-real-ℝ⁺ = pr2
```

## Properties

### There exists a positive rational number in the lower cut of every positive real number

```agda
exists-ℚ⁺-in-lower-cut-ℝ⁺ :
  {l : Level} → (x : ℝ⁺ l) →
  exists ℚ⁺ (λ p → lower-cut-ℝ (real-ℝ⁺ x) (rational-ℚ⁺ p))
exists-ℚ⁺-in-lower-cut-ℝ⁺ (x , pos-x) =
  elim-exists
    ( ∃ ℚ⁺ (λ p → lower-cut-ℝ x (rational-ℚ⁺ p)))
    ( λ p (0<p , p<x) → intro-exists (p , is-positive-le-zero-ℚ p 0<p) p<x)
    ( pos-x)
```

### Addition with a positive real number is a strictly inflationary map

```agda
abstract
  le-left-add-real-ℝ⁺ :
    {l1 l2 : Level} → (x : ℝ l1) (d : ℝ⁺ l2) → le-ℝ x (x +ℝ real-ℝ⁺ d)
  le-left-add-real-ℝ⁺ x d⁺@(d , pos-d) =
    do
      r⁺@(r , _) , r<d ← exists-ℚ⁺-in-lower-cut-ℝ⁺ d⁺
      (p , q) , (q<p+r , p<x , x<q) ←
        is-arithmetically-located-lower-upper-real-ℝ x r⁺
      intro-exists
        ( q)
        ( x<q ,
          intro-exists
            ( p , q -ℚ p)
            ( p<x ,
              le-lower-cut-ℝ
                ( d)
                ( q -ℚ p)
                ( r)
                ( binary-tr
                  ( le-ℚ)
                  ( commutative-add-ℚ (neg-ℚ p) q)
                  ( is-retraction-left-div-Group group-add-ℚ p r)
                  ( preserves-le-right-add-ℚ (neg-ℚ p) q (p +ℚ r) q<p+r))
                ( r<d) ,
              inv (is-identity-right-conjugation-Ab abelian-group-add-ℚ p q)))
    where open do-syntax-trunc-Prop (le-ℝ-Prop x (x +ℝ d))

le-right-add-real-ℝ⁺ :
  {l1 l2 : Level} → (x : ℝ l1) (d : ℝ⁺ l2) → le-ℝ x (real-ℝ⁺ d +ℝ x)
le-right-add-real-ℝ⁺ x d =
  tr (le-ℝ x) (commutative-add-ℝ x (real-ℝ⁺ d)) (le-left-add-real-ℝ⁺ x d)
```

### Subtraction by a positive real number is a strictly deflationary map

```agda
abstract
  le-diff-real-ℝ⁺ :
    {l1 l2 : Level} → (x : ℝ l1) (d : ℝ⁺ l2) → le-ℝ (x -ℝ real-ℝ⁺ d) x
  le-diff-real-ℝ⁺ x d⁺@(d , _) =
    preserves-le-right-sim-ℝ
      ( x -ℝ d)
      ( (x -ℝ d) +ℝ d)
      ( x)
      ( tr
        ( λ y → sim-ℝ y x)
        ( right-swap-add-ℝ x d (neg-ℝ d))
        ( cancel-right-add-ℝ x d))
      ( le-left-add-real-ℝ⁺ (x -ℝ d) d⁺)
```

### The difference of a real number with a lesser real number is positive

```agda
module _
  {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2) (H : le-ℝ x y)
  where

  is-positive-diff-le-ℝ : is-positive-ℝ (y -ℝ x)
  is-positive-diff-le-ℝ =
    preserves-le-left-sim-ℝ
      ( y -ℝ x)
      ( x -ℝ x)
      ( zero-ℝ)
      ( right-inverse-law-add-ℝ x)
      ( preserves-le-right-add-ℝ (neg-ℝ x) x y H)

  positive-diff-le-ℝ : ℝ⁺ (l1 ⊔ l2)
  positive-diff-le-ℝ = y -ℝ x , is-positive-diff-le-ℝ
```

### The real embedding of a positive rational number is positive

```agda
is-positive-real-positive-ℚ :
  (q : ℚ) → is-positive-ℚ q → is-positive-ℝ (real-ℚ q)
is-positive-real-positive-ℚ q pos-q =
  preserves-le-real-ℚ zero-ℚ q (le-zero-is-positive-ℚ q pos-q)

positive-real-ℚ⁺ : ℚ⁺ → ℝ⁺ lzero
positive-real-ℚ⁺ (q , pos-q) = (real-ℚ q , is-positive-real-positive-ℚ q pos-q)
```
