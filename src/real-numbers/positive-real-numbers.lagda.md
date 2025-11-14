# Positive real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.positive-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-positive-rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.inhabited-subtypes
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.strict-inequalities-addition-and-subtraction-real-numbers
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

### Positivity is preserved by similarity

```agda
abstract
  is-positive-sim-ℝ :
    {l1 l2 : Level} {x : ℝ l1} {y : ℝ l2} →
    is-positive-ℝ x → sim-ℝ x y → is-positive-ℝ y
  is-positive-sim-ℝ {x = x} {y = y} 0<x x~y =
    preserves-le-right-sim-ℝ zero-ℝ x y x~y 0<x
```

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

### A real number is positive if it is greater than a positive real number

```agda
abstract
  is-positive-le-ℝ⁺ :
    {l1 l2 : Level} (x : ℝ⁺ l1) (y : ℝ l2) → le-ℝ (real-ℝ⁺ x) y →
    is-positive-ℝ y
  is-positive-le-ℝ⁺ (x , 0<x) y x<y = transitive-le-ℝ zero-ℝ x y x<y 0<x
```

### A real number is positive if and only if zero is in its lower cut

```agda
module _
  {l : Level} (x : ℝ l)
  where

  abstract
    is-positive-iff-zero-in-lower-cut-ℝ :
      is-positive-ℝ x ↔ is-in-lower-cut-ℝ x zero-ℚ
    is-positive-iff-zero-in-lower-cut-ℝ =
      inv-iff (le-real-iff-is-in-lower-cut-ℝ x)

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

### `x` is positive if and only if there exists a positive rational number it is not less than or equal to

```agda
module _
  {l : Level} (x : ℝ l)
  where

  abstract
    is-positive-exists-not-le-positive-rational-ℝ :
      exists ℚ⁺ (λ q → ¬' (leq-prop-ℝ x (real-ℚ⁺ q))) →
      is-positive-ℝ x
    is-positive-exists-not-le-positive-rational-ℝ ∃q =
      let open do-syntax-trunc-Prop (is-positive-prop-ℝ x)
      in do
        (q⁺@(q , _) , x≰q) ← ∃q
        let p⁺@(p , _) = mediant-zero-ℚ⁺ q⁺
        elim-disjunction
          ( is-positive-prop-ℝ x)
          ( is-positive-le-ℝ⁺ (positive-real-ℚ⁺ p⁺) x)
          ( λ x<q → ex-falso (x≰q (leq-le-ℝ x<q)))
          ( is-located-le-ℝ x p q (le-mediant-zero-ℚ⁺ q⁺))

    exists-not-le-positive-rational-is-positive-ℝ :
      is-positive-ℝ x →
      exists ℚ⁺ (λ q → ¬' (leq-prop-ℝ x (real-ℚ⁺ q)))
    exists-not-le-positive-rational-is-positive-ℝ 0<x =
      let open do-syntax-trunc-Prop (∃ ℚ⁺ (λ q → ¬' (leq-prop-ℝ x (real-ℚ⁺ q))))
      in do
        (q , 0<q , q<x) ← dense-rational-le-ℝ _ _ 0<x
        intro-exists
          ( q , is-positive-le-zero-ℚ (reflects-le-real-ℚ 0<q))
          ( not-leq-le-ℝ _ _ q<x)
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

### Raising the universe level of positive real numbers

```agda
raise-ℝ⁺ : {l1 : Level} (l : Level) → ℝ⁺ l1 → ℝ⁺ (l ⊔ l1)
raise-ℝ⁺ l (x , 0<x) =
  ( raise-ℝ l x , preserves-le-right-sim-ℝ zero-ℝ x _ (sim-raise-ℝ _ _) 0<x)
```
