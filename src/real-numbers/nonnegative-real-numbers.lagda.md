# Nonnegative real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.nonnegative-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.nonnegative-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers

open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import logic.functoriality-existential-quantification

open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.saturation-inequality-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.strict-inequality-real-numbers
```

</details>

## Idea

A real number `x` is
{{#concept "nonnegative" Disambiguation="real number" Agda=is-nonnegative-ℝ}} if
`0 ≤ x`.

## Definitions

```agda
is-nonnegative-ℝ : {l : Level} → ℝ l → UU l
is-nonnegative-ℝ = leq-ℝ zero-ℝ

is-nonnegative-prop-ℝ : {l : Level} → ℝ l → Prop l
is-nonnegative-prop-ℝ = leq-prop-ℝ zero-ℝ

nonnegative-ℝ : (l : Level) → UU (lsuc l)
nonnegative-ℝ l = type-subtype (is-nonnegative-prop-ℝ {l})

ℝ⁰⁺ : (l : Level) → UU (lsuc l)
ℝ⁰⁺ = nonnegative-ℝ

real-ℝ⁰⁺ : {l : Level} → ℝ⁰⁺ l → ℝ l
real-ℝ⁰⁺ = pr1

is-nonnegative-real-ℝ⁰⁺ :
  {l : Level} (x : ℝ⁰⁺ l) → is-nonnegative-ℝ (real-ℝ⁰⁺ x)
is-nonnegative-real-ℝ⁰⁺ = pr2
```

## Properties

### The nonnegative real numbers form a set

```agda
ℝ⁰⁺-Set : (l : Level) → Set (lsuc l)
ℝ⁰⁺-Set l = set-subset (ℝ-Set l) is-nonnegative-prop-ℝ
```

### Equality in the nonnegative real numbers

```agda
eq-ℝ⁰⁺ : {l : Level} (x y : ℝ⁰⁺ l) → real-ℝ⁰⁺ x ＝ real-ℝ⁰⁺ y → x ＝ y
eq-ℝ⁰⁺ _ _ = eq-type-subtype is-nonnegative-prop-ℝ
```

### The canonical embedding from nonnegative rational numbers to nonnegative real numbers

```agda
abstract
  is-nonnegative-real-ℚ⁰⁺ : (q : ℚ⁰⁺) → is-nonnegative-ℝ (real-ℚ⁰⁺ q)
  is-nonnegative-real-ℚ⁰⁺ (q , nonneg-q) =
    preserves-leq-real-ℚ zero-ℚ q (leq-zero-is-nonnegative-ℚ q nonneg-q)

nonnegative-real-ℚ⁰⁺ : ℚ⁰⁺ → ℝ⁰⁺ lzero
nonnegative-real-ℚ⁰⁺ q = (real-ℚ⁰⁺ q , is-nonnegative-real-ℚ⁰⁺ q)

nonnegative-real-ℚ⁺ : ℚ⁺ → ℝ⁰⁺ lzero
nonnegative-real-ℚ⁺ q = nonnegative-real-ℚ⁰⁺ (nonnegative-ℚ⁺ q)
```

### Important nonnegative real numbers

```agda
zero-ℝ⁰⁺ : ℝ⁰⁺ lzero
zero-ℝ⁰⁺ = nonnegative-real-ℚ⁰⁺ zero-ℚ⁰⁺

one-ℝ⁰⁺ : ℝ⁰⁺ lzero
one-ℝ⁰⁺ = nonnegative-real-ℚ⁰⁺ one-ℚ⁰⁺
```

### Similarity of nonnegative real numbers

```agda
module _
  {l1 l2 : Level} (x : ℝ⁰⁺ l1) (y : ℝ⁰⁺ l2)
  where

  sim-prop-ℝ⁰⁺ : Prop (l1 ⊔ l2)
  sim-prop-ℝ⁰⁺ = sim-prop-ℝ (real-ℝ⁰⁺ x) (real-ℝ⁰⁺ y)

  sim-ℝ⁰⁺ : UU (l1 ⊔ l2)
  sim-ℝ⁰⁺ = sim-ℝ (real-ℝ⁰⁺ x) (real-ℝ⁰⁺ y)

infix 6 _~ℝ⁰⁺_
_~ℝ⁰⁺_ : {l1 l2 : Level} → ℝ⁰⁺ l1 → ℝ⁰⁺ l2 → UU (l1 ⊔ l2)
_~ℝ⁰⁺_ = sim-ℝ⁰⁺

sim-zero-prop-ℝ⁰⁺ : {l : Level} → ℝ⁰⁺ l → Prop l
sim-zero-prop-ℝ⁰⁺ = sim-prop-ℝ⁰⁺ zero-ℝ⁰⁺

sim-zero-ℝ⁰⁺ : {l : Level} → ℝ⁰⁺ l → UU l
sim-zero-ℝ⁰⁺ = sim-ℝ⁰⁺ zero-ℝ⁰⁺

eq-sim-ℝ⁰⁺ : {l : Level} (x y : ℝ⁰⁺ l) → sim-ℝ⁰⁺ x y → x ＝ y
eq-sim-ℝ⁰⁺ x y x~y = eq-ℝ⁰⁺ x y (eq-sim-ℝ {x = real-ℝ⁰⁺ x} {y = real-ℝ⁰⁺ y} x~y)
```

#### Similarity is symmetric

```agda
abstract
  symmetric-sim-ℝ⁰⁺ :
    {l1 l2 : Level} → (x : ℝ⁰⁺ l1) (y : ℝ⁰⁺ l2) → x ~ℝ⁰⁺ y → y ~ℝ⁰⁺ x
  symmetric-sim-ℝ⁰⁺ _ _ = symmetric-sim-ℝ
```

### Inequality on nonnegative real numbers

```agda
module _
  {l1 l2 : Level} (x : ℝ⁰⁺ l1) (y : ℝ⁰⁺ l2)
  where

  leq-prop-ℝ⁰⁺ : Prop (l1 ⊔ l2)
  leq-prop-ℝ⁰⁺ = leq-prop-ℝ (real-ℝ⁰⁺ x) (real-ℝ⁰⁺ y)

  leq-ℝ⁰⁺ : UU (l1 ⊔ l2)
  leq-ℝ⁰⁺ = type-Prop leq-prop-ℝ⁰⁺
```

### Zero is less than or equal to every nonnegative real number

```agda
leq-zero-ℝ⁰⁺ : {l : Level} (x : ℝ⁰⁺ l) → leq-ℝ⁰⁺ zero-ℝ⁰⁺ x
leq-zero-ℝ⁰⁺ = is-nonnegative-real-ℝ⁰⁺
```

### Similarity preserves inequality

```agda
module _
  {l1 l2 l3 : Level} (z : ℝ⁰⁺ l1) (x : ℝ⁰⁺ l2) (y : ℝ⁰⁺ l3) (x~y : sim-ℝ⁰⁺ x y)
  where

  abstract
    preserves-leq-left-sim-ℝ⁰⁺ : leq-ℝ⁰⁺ x z → leq-ℝ⁰⁺ y z
    preserves-leq-left-sim-ℝ⁰⁺ =
      preserves-leq-left-sim-ℝ (real-ℝ⁰⁺ z) _ _ x~y
```

### Inequality is transitive

```agda
module _
  {l1 l2 l3 : Level} (x : ℝ⁰⁺ l1) (y : ℝ⁰⁺ l2) (z : ℝ⁰⁺ l3)
  where

  transitive-leq-ℝ⁰⁺ : leq-ℝ⁰⁺ y z → leq-ℝ⁰⁺ x y → leq-ℝ⁰⁺ x z
  transitive-leq-ℝ⁰⁺ = transitive-leq-ℝ (real-ℝ⁰⁺ x) (real-ℝ⁰⁺ y) (real-ℝ⁰⁺ z)
```

### Strict inequality on nonnegative real numbers

```agda
module _
  {l1 l2 : Level} (x : ℝ⁰⁺ l1) (y : ℝ⁰⁺ l2)
  where

  le-prop-ℝ⁰⁺ : Prop (l1 ⊔ l2)
  le-prop-ℝ⁰⁺ = le-prop-ℝ (real-ℝ⁰⁺ x) (real-ℝ⁰⁺ y)

  le-ℝ⁰⁺ : UU (l1 ⊔ l2)
  le-ℝ⁰⁺ = type-Prop le-prop-ℝ⁰⁺
```

### The canonical embedding of nonnegative rational numbers to nonnegative reals preserves strict inequality

```agda
abstract
  preserves-le-nonnegative-real-ℚ⁰⁺ :
    (p q : ℚ⁰⁺) →
    le-ℚ⁰⁺ p q → le-ℝ⁰⁺ (nonnegative-real-ℚ⁰⁺ p) (nonnegative-real-ℚ⁰⁺ q)
  preserves-le-nonnegative-real-ℚ⁰⁺ p q = preserves-le-real-ℚ _ _
```

### Similarity preserves strict inequality

```agda
module _
  {l1 l2 l3 : Level} (z : ℝ⁰⁺ l1) (x : ℝ⁰⁺ l2) (y : ℝ⁰⁺ l3) (x~y : sim-ℝ⁰⁺ x y)
  where

  abstract
    preserves-le-left-sim-ℝ⁰⁺ : le-ℝ⁰⁺ x z → le-ℝ⁰⁺ y z
    preserves-le-left-sim-ℝ⁰⁺ =
      preserves-le-left-sim-ℝ (real-ℝ⁰⁺ z) _ _ x~y
```

### Concatenation of inequality and strict inequality

```agda
module _
  {l1 l2 l3 : Level} (x : ℝ⁰⁺ l1) (y : ℝ⁰⁺ l2) (z : ℝ⁰⁺ l3)
  where

  abstract
    concatenate-leq-le-ℝ⁰⁺ : leq-ℝ⁰⁺ x y → le-ℝ⁰⁺ y z → le-ℝ⁰⁺ x z
    concatenate-leq-le-ℝ⁰⁺ =
      concatenate-leq-le-ℝ (real-ℝ⁰⁺ x) (real-ℝ⁰⁺ y) (real-ℝ⁰⁺ z)
```

### Every nonnegative real number is less than some positive rational number

```agda
module _
  {l : Level} (x : ℝ⁰⁺ l)
  where

  abstract
    le-some-positive-rational-ℝ⁰⁺ :
      exists ℚ⁺ (λ q → le-prop-ℝ⁰⁺ x (nonnegative-real-ℚ⁺ q))
    le-some-positive-rational-ℝ⁰⁺ =
      let
        open
          do-syntax-trunc-Prop
            ( ∃ ℚ⁺ (λ q → le-prop-ℝ⁰⁺ x (nonnegative-real-ℚ⁺ q)))
      in do
        (q , x<q) ← le-some-rational-ℝ (real-ℝ⁰⁺ x)
        intro-exists
          ( q ,
            is-positive-le-zero-ℚ
              ( q)
              ( reflects-le-real-ℚ zero-ℚ q
                ( concatenate-leq-le-ℝ
                  ( zero-ℝ)
                  ( real-ℝ⁰⁺ x)
                  ( real-ℚ q)
                  ( is-nonnegative-real-ℝ⁰⁺ x)
                  ( x<q))))
          ( x<q)
```

### Addition on nonnegative real numbers

```agda
module _
  {l1 l2 : Level} (x : ℝ⁰⁺ l1) (y : ℝ⁰⁺ l2)
  where

  real-add-ℝ⁰⁺ : ℝ (l1 ⊔ l2)
  real-add-ℝ⁰⁺ = real-ℝ⁰⁺ x +ℝ real-ℝ⁰⁺ y

  abstract
    is-nonnegative-real-add-ℝ⁰⁺ : is-nonnegative-ℝ real-add-ℝ⁰⁺
    is-nonnegative-real-add-ℝ⁰⁺ =
      tr
        ( λ z → leq-ℝ z (real-ℝ⁰⁺ x +ℝ real-ℝ⁰⁺ y))
        ( left-unit-law-add-ℝ zero-ℝ)
        ( preserves-leq-add-ℝ
          ( zero-ℝ)
          ( real-ℝ⁰⁺ x)
          ( zero-ℝ)
          ( real-ℝ⁰⁺ y)
          ( is-nonnegative-real-ℝ⁰⁺ x)
          ( is-nonnegative-real-ℝ⁰⁺ y))

  add-ℝ⁰⁺ : ℝ⁰⁺ (l1 ⊔ l2)
  add-ℝ⁰⁺ = (real-add-ℝ⁰⁺ , is-nonnegative-real-add-ℝ⁰⁺)

infixl 35 _+ℝ⁰⁺_

_+ℝ⁰⁺_ : {l1 l2 : Level} → ℝ⁰⁺ l1 → ℝ⁰⁺ l2 → ℝ⁰⁺ (l1 ⊔ l2)
_+ℝ⁰⁺_ = add-ℝ⁰⁺
```

### Unit laws for addition

```agda
module _
  {l : Level} (x : ℝ⁰⁺ l)
  where

  abstract
    left-unit-law-add-ℝ⁰⁺ : zero-ℝ⁰⁺ +ℝ⁰⁺ x ＝ x
    left-unit-law-add-ℝ⁰⁺ = eq-ℝ⁰⁺ _ _ (left-unit-law-add-ℝ _)

    right-unit-law-add-ℝ⁰⁺ : x +ℝ⁰⁺ zero-ℝ⁰⁺ ＝ x
    right-unit-law-add-ℝ⁰⁺ = eq-ℝ⁰⁺ _ _ (right-unit-law-add-ℝ _)
```

### Addition preserves inequality

```agda
module _
  {l1 l2 l3 l4 : Level} (x : ℝ⁰⁺ l1) (y : ℝ⁰⁺ l2) (z : ℝ⁰⁺ l3) (w : ℝ⁰⁺ l4)
  where

  abstract
    preserves-leq-add-ℝ⁰⁺ :
      leq-ℝ⁰⁺ x y → leq-ℝ⁰⁺ z w → leq-ℝ⁰⁺ (x +ℝ⁰⁺ z) (y +ℝ⁰⁺ w)
    preserves-leq-add-ℝ⁰⁺ =
      preserves-leq-add-ℝ (real-ℝ⁰⁺ x) (real-ℝ⁰⁺ y) (real-ℝ⁰⁺ z) (real-ℝ⁰⁺ w)
```

### If `x ≤ y + ε` for every `ε : ℚ⁺`, then `x ≤ y`

```agda
module _
  {l1 l2 : Level} (x : ℝ⁰⁺ l1) (y : ℝ⁰⁺ l2)
  where

  abstract
    saturated-leq-ℝ⁰⁺ :
      ((ε : ℚ⁺) → leq-ℝ⁰⁺ x (y +ℝ⁰⁺ nonnegative-real-ℚ⁺ ε)) →
      leq-ℝ⁰⁺ x y
    saturated-leq-ℝ⁰⁺ = saturated-leq-ℝ (real-ℝ⁰⁺ x) (real-ℝ⁰⁺ y)
```

### If a nonnegative real number is less than or equal to all positive rational numbers, it is similar to zero

```agda
sim-zero-le-positive-rational-ℝ⁰⁺ :
  {l : Level} (x : ℝ⁰⁺ l) →
  ((ε : ℚ⁺) → leq-ℝ⁰⁺ x (nonnegative-real-ℚ⁺ ε)) →
  sim-zero-ℝ⁰⁺ x
sim-zero-le-positive-rational-ℝ⁰⁺ x H =
  sim-sim-leq-ℝ
    ( leq-zero-ℝ⁰⁺ x ,
      saturated-leq-ℝ⁰⁺
        ( x)
        ( zero-ℝ⁰⁺)
        ( λ ε → inv-tr (leq-ℝ⁰⁺ x) (left-unit-law-add-ℝ⁰⁺ _) (H ε)))
```

### Addition preserves strict inequality

```agda
module _
  {l1 l2 l3 l4 : Level} (x : ℝ⁰⁺ l1) (y : ℝ⁰⁺ l2) (z : ℝ⁰⁺ l3) (w : ℝ⁰⁺ l4)
  where

  abstract
    preserves-le-add-ℝ⁰⁺ :
      le-ℝ⁰⁺ x y → le-ℝ⁰⁺ z w → le-ℝ⁰⁺ (x +ℝ⁰⁺ z) (y +ℝ⁰⁺ w)
    preserves-le-add-ℝ⁰⁺ =
      preserves-le-add-ℝ (real-ℝ⁰⁺ x) (real-ℝ⁰⁺ y) (real-ℝ⁰⁺ z) (real-ℝ⁰⁺ w)
```

### The canonical embedding of nonnegative rational numbers to nonnegative real numbers preserves addition

```agda
abstract
  add-nonnegative-real-ℚ⁰⁺ :
    (p q : ℚ⁰⁺) →
    nonnegative-real-ℚ⁰⁺ p +ℝ⁰⁺ nonnegative-real-ℚ⁰⁺ q ＝
    nonnegative-real-ℚ⁰⁺ (p +ℚ⁰⁺ q)
  add-nonnegative-real-ℚ⁰⁺ p q =
    eq-ℝ⁰⁺ _ _ (add-real-ℚ (rational-ℚ⁰⁺ p) (rational-ℚ⁰⁺ q))
```

### The canonical embedding of positive rational numbers to nonnegative real numbers preserves addition

```agda
abstract
  add-nonnegative-real-ℚ⁺ :
    (p q : ℚ⁺) →
    nonnegative-real-ℚ⁺ p +ℝ⁰⁺ nonnegative-real-ℚ⁺ q ＝
    nonnegative-real-ℚ⁺ (p +ℚ⁺ q)
  add-nonnegative-real-ℚ⁺ p q =
    eq-ℝ⁰⁺ _ _ (add-real-ℚ (rational-ℚ⁺ p) (rational-ℚ⁺ q))
```
