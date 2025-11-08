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
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.inhabited-subtypes
open import foundation.logical-equivalences
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
open import real-numbers.strict-inequalities-addition-real-numbers
open import real-numbers.strict-inequality-real-numbers
```

</details>

## Idea

A [real number](real-numbers.dedekind-real-numbers.md) is
{{#concept "positive" Disambiguation="real number" Agda=is-positive-ℝ}} if zero
is [strictly less than](real-numbers.strict-inequality-real-numbers.md) it.

## Definitions

### The positivity predicate on real numbers

```agda
is-positive-prop-ℝ : {l : Level} → ℝ l → Prop l
is-positive-prop-ℝ = le-prop-ℝ zero-ℝ

is-positive-ℝ : {l : Level} → ℝ l → UU l
is-positive-ℝ x = type-Prop (is-positive-prop-ℝ x)
```

### The type of positive real numbers

```agda
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

### Dedekind cuts of positive real numbers

```agda
lower-cut-ℝ⁺ : {l : Level} → ℝ⁺ l → subtype l ℚ
lower-cut-ℝ⁺ (x , _) = lower-cut-ℝ x

is-in-lower-cut-ℝ⁺ : {l : Level} → ℝ⁺ l → ℚ → UU l
is-in-lower-cut-ℝ⁺ (x , _) = is-in-lower-cut-ℝ x

is-rounded-lower-cut-ℝ⁺ :
  {l : Level} (x : ℝ⁺ l) (q : ℚ) →
  is-in-lower-cut-ℝ⁺ x q ↔ exists ℚ (λ r → (le-ℚ-Prop q r) ∧ (lower-cut-ℝ⁺ x r))
is-rounded-lower-cut-ℝ⁺ (x , _) = is-rounded-lower-cut-ℝ x

upper-cut-ℝ⁺ : {l : Level} → ℝ⁺ l → subtype l ℚ
upper-cut-ℝ⁺ (x , _) = upper-cut-ℝ x

is-in-upper-cut-ℝ⁺ : {l : Level} → ℝ⁺ l → ℚ → UU l
is-in-upper-cut-ℝ⁺ (x , _) = is-in-upper-cut-ℝ x

is-inhabited-upper-cut-ℝ⁺ :
  {l : Level} (x : ℝ⁺ l) → is-inhabited-subtype (upper-cut-ℝ⁺ x)
is-inhabited-upper-cut-ℝ⁺ (x , _) = is-inhabited-upper-cut-ℝ x

is-rounded-upper-cut-ℝ⁺ :
  {l : Level} (x : ℝ⁺ l) (r : ℚ) →
  is-in-upper-cut-ℝ⁺ x r ↔ exists ℚ (λ q → (le-ℚ-Prop q r) ∧ (upper-cut-ℝ⁺ x q))
is-rounded-upper-cut-ℝ⁺ (x , _) = is-rounded-upper-cut-ℝ x

le-lower-upper-cut-ℝ⁺ :
  {l : Level} (x : ℝ⁺ l) {p q : ℚ} →
  is-in-lower-cut-ℝ⁺ x p → is-in-upper-cut-ℝ⁺ x q → le-ℚ p q
le-lower-upper-cut-ℝ⁺ (x , _) = le-lower-upper-cut-ℝ x
```

### Equality of positive real numbers

```agda
eq-ℝ⁺ : {l : Level} (x y : ℝ⁺ l) → (real-ℝ⁺ x ＝ real-ℝ⁺ y) → x ＝ y
eq-ℝ⁺ _ _ = eq-type-subtype is-positive-prop-ℝ
```

### A real number is positive if and only if zero is in its lower cut

```agda
module _
  {l : Level} (x : ℝ l)
  where

  abstract
    is-positive-iff-zero-in-lower-cut-ℝ :
      is-positive-ℝ x ↔ is-in-lower-cut-ℝ x zero-ℚ
    is-positive-iff-zero-in-lower-cut-ℝ = inv-iff (le-real-iff-lower-cut-ℚ x)

    is-positive-zero-in-lower-cut-ℝ :
      is-in-lower-cut-ℝ x zero-ℚ → is-positive-ℝ x
    is-positive-zero-in-lower-cut-ℝ =
      backward-implication is-positive-iff-zero-in-lower-cut-ℝ

abstract
  zero-in-lower-cut-ℝ⁺ : {l : Level} (x : ℝ⁺ l) → is-in-lower-cut-ℝ⁺ x zero-ℚ
  zero-in-lower-cut-ℝ⁺ (x , is-pos-x) =
    forward-implication (is-positive-iff-zero-in-lower-cut-ℝ x) is-pos-x
```

### A real number is positive if and only if there is a positive rational number in its lower cut

```agda
module _
  {l : Level} (x : ℝ l)
  where

  abstract opaque
    unfolding le-ℝ real-ℚ

    exists-ℚ⁺-in-lower-cut-is-positive-ℝ :
      is-positive-ℝ x → exists ℚ⁺ (λ p → lower-cut-ℝ x (rational-ℚ⁺ p))
    exists-ℚ⁺-in-lower-cut-is-positive-ℝ =
      elim-exists
        ( ∃ ℚ⁺ (λ p → lower-cut-ℝ x (rational-ℚ⁺ p)))
        ( λ p (0<p , p<x) → intro-exists (p , is-positive-le-zero-ℚ 0<p) p<x)

    is-positive-exists-ℚ⁺-in-lower-cut-ℝ :
      exists ℚ⁺ (λ p → lower-cut-ℝ x (rational-ℚ⁺ p)) →
      is-positive-ℝ x
    is-positive-exists-ℚ⁺-in-lower-cut-ℝ =
      elim-exists
        ( is-positive-prop-ℝ x)
        ( λ (p , pos-p) p<x →
          intro-exists p (le-zero-is-positive-ℚ pos-p , p<x))

  is-positive-iff-exists-ℚ⁺-in-lower-cut-ℝ :
    is-positive-ℝ x ↔ exists ℚ⁺ (λ p → lower-cut-ℝ x (rational-ℚ⁺ p))
  is-positive-iff-exists-ℚ⁺-in-lower-cut-ℝ =
    ( exists-ℚ⁺-in-lower-cut-is-positive-ℝ ,
      is-positive-exists-ℚ⁺-in-lower-cut-ℝ)

exists-ℚ⁺-in-lower-cut-ℝ⁺ :
  {l : Level} (x : ℝ⁺ l) → exists ℚ⁺ (λ p → lower-cut-ℝ⁺ x (rational-ℚ⁺ p))
exists-ℚ⁺-in-lower-cut-ℝ⁺ = ind-Σ exists-ℚ⁺-in-lower-cut-is-positive-ℝ
```

### Addition with a positive real number is a strictly inflationary map

```agda
abstract opaque
  unfolding add-ℝ le-ℝ

  le-left-add-real-ℝ⁺ :
    {l1 l2 : Level} → (x : ℝ l1) (d : ℝ⁺ l2) → le-ℝ x (x +ℝ real-ℝ⁺ d)
  le-left-add-real-ℝ⁺ x d⁺@(d , pos-d) =
    tr
      ( λ y → le-ℝ y (x +ℝ d))
      ( right-unit-law-add-ℝ x)
      ( preserves-le-left-add-ℝ x zero-ℝ d pos-d)

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
        ( cancel-right-add-diff-ℝ x d))
      ( le-left-add-real-ℝ⁺ (x -ℝ d) d⁺)
```

### `x < y` if and only if `y - x` is positive

```agda
module _
  {l1 l2 : Level} {x : ℝ l1} {y : ℝ l2} (H : le-ℝ x y)
  where

  abstract
    is-positive-diff-le-ℝ : is-positive-ℝ (y -ℝ x)
    is-positive-diff-le-ℝ =
      preserves-le-left-sim-ℝ
        ( y -ℝ x)
        ( x -ℝ x)
        ( zero-ℝ)
        ( right-inverse-law-add-ℝ x)
        ( preserves-le-right-add-ℝ (neg-ℝ x) x y H)

  positive-diff-le-ℝ : ℝ⁺ (l1 ⊔ l2)
  positive-diff-le-ℝ = (y -ℝ x , is-positive-diff-le-ℝ)

abstract
  le-is-positive-diff-ℝ :
    {l1 l2 : Level} {x : ℝ l1} {y : ℝ l2} → is-positive-ℝ (y -ℝ x) → le-ℝ x y
  le-is-positive-diff-ℝ {x = x} {y = y} 0<y-x =
    tr
      ( λ z → le-ℝ z y)
      ( left-unit-law-add-ℝ x)
      ( le-transpose-right-diff-ℝ zero-ℝ y x 0<y-x)
```

### The canonical embedding of rational numbers preserves positivity

```agda
abstract
  preserves-is-positive-real-ℚ :
    {q : ℚ} → is-positive-ℚ q → is-positive-ℝ (real-ℚ q)
  preserves-is-positive-real-ℚ pos-q =
    preserves-le-real-ℚ (le-zero-is-positive-ℚ pos-q)

  reflects-is-positive-real-ℚ :
    {q : ℚ} → is-positive-ℝ (real-ℚ q) → is-positive-ℚ q
  reflects-is-positive-real-ℚ {q} 0<qℝ =
    is-positive-le-zero-ℚ (reflects-le-real-ℚ 0<qℝ)

positive-real-ℚ⁺ : ℚ⁺ → ℝ⁺ lzero
positive-real-ℚ⁺ (q , pos-q) = (real-ℚ q , preserves-is-positive-real-ℚ pos-q)

one-ℝ⁺ : ℝ⁺ lzero
one-ℝ⁺ = positive-real-ℚ⁺ one-ℚ⁺
```

### Any rational number in the upper cut of a positive real number is positive

```agda
abstract
  is-positive-is-in-upper-cut-ℝ⁺ :
    {l : Level} (x : ℝ⁺ l) {q : ℚ} → is-in-upper-cut-ℝ⁺ x q → is-positive-ℚ q
  is-positive-is-in-upper-cut-ℝ⁺ x⁺@(x , _) x<q =
    is-positive-le-zero-ℚ
      ( le-lower-upper-cut-ℝ x (zero-in-lower-cut-ℝ⁺ x⁺) x<q)
```
