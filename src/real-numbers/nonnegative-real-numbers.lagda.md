# Nonnegative real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.nonnegative-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.negative-rational-numbers
open import elementary-number-theory.nonnegative-rational-numbers
open import elementary-number-theory.positive-and-negative-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers
open import elementary-number-theory.unit-fractions-rational-numbers

open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.functoriality-propositional-truncation
open import foundation.identity-types
open import foundation.inhabited-subtypes
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import logic.functoriality-existential-quantification

open import metric-spaces.metric-spaces

open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.inequalities-addition-and-subtraction-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-real-numbers
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

### Dedekind cuts of nonnegative real numbers

```agda
lower-cut-ℝ⁰⁺ : {l : Level} → ℝ⁰⁺ l → subtype l ℚ
lower-cut-ℝ⁰⁺ (x , _) = lower-cut-ℝ x

is-in-lower-cut-ℝ⁰⁺ : {l : Level} → ℝ⁰⁺ l → ℚ → UU l
is-in-lower-cut-ℝ⁰⁺ (x , _) = is-in-lower-cut-ℝ x

is-rounded-lower-cut-ℝ⁰⁺ :
  {l : Level} → (x : ℝ⁰⁺ l) (q : ℚ) →
  (is-in-lower-cut-ℝ⁰⁺ x q ↔ exists ℚ (λ r → le-ℚ-Prop q r ∧ lower-cut-ℝ⁰⁺ x r))
is-rounded-lower-cut-ℝ⁰⁺ (x , _) = is-rounded-lower-cut-ℝ x

upper-cut-ℝ⁰⁺ : {l : Level} → ℝ⁰⁺ l → subtype l ℚ
upper-cut-ℝ⁰⁺ (x , _) = upper-cut-ℝ x

is-in-upper-cut-ℝ⁰⁺ : {l : Level} → ℝ⁰⁺ l → ℚ → UU l
is-in-upper-cut-ℝ⁰⁺ (x , _) = is-in-upper-cut-ℝ x

is-inhabited-upper-cut-ℝ⁰⁺ :
  {l : Level} (x : ℝ⁰⁺ l) → is-inhabited-subtype (upper-cut-ℝ⁰⁺ x)
is-inhabited-upper-cut-ℝ⁰⁺ (x , _) = is-inhabited-upper-cut-ℝ x

is-rounded-upper-cut-ℝ⁰⁺ :
  {l : Level} (x : ℝ⁰⁺ l) (r : ℚ) →
  (is-in-upper-cut-ℝ⁰⁺ x r ↔ exists ℚ (λ q → le-ℚ-Prop q r ∧ upper-cut-ℝ⁰⁺ x q))
is-rounded-upper-cut-ℝ⁰⁺ (x , _) = is-rounded-upper-cut-ℝ x
```

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
  preserves-is-nonnegative-real-ℚ :
    {q : ℚ} → is-nonnegative-ℚ q → is-nonnegative-ℝ (real-ℚ q)
  preserves-is-nonnegative-real-ℚ is-nonneg-q =
    preserves-leq-real-ℚ (leq-zero-is-nonnegative-ℚ is-nonneg-q)

  reflects-is-nonnegative-real-ℚ :
    {q : ℚ} → is-nonnegative-ℝ (real-ℚ q) → is-nonnegative-ℚ q
  reflects-is-nonnegative-real-ℚ 0≤qℝ =
    is-nonnegative-leq-zero-ℚ (reflects-leq-real-ℚ 0≤qℝ)

nonnegative-real-ℚ⁰⁺ : ℚ⁰⁺ → ℝ⁰⁺ lzero
nonnegative-real-ℚ⁰⁺ (q , is-nonneg-q) =
  ( real-ℚ q , preserves-is-nonnegative-real-ℚ is-nonneg-q)

nonnegative-real-ℚ⁺ : ℚ⁺ → ℝ⁰⁺ lzero
nonnegative-real-ℚ⁺ q = nonnegative-real-ℚ⁰⁺ (nonnegative-ℚ⁺ q)
```

### The canonical embedding of natural numbers in the nonnegative real numbers

```agda
nonnegative-real-ℕ : ℕ → ℝ⁰⁺ lzero
nonnegative-real-ℕ n = nonnegative-real-ℚ⁰⁺ (nonnegative-rational-ℕ n)
```

### Important nonnegative real numbers

```agda
zero-ℝ⁰⁺ : ℝ⁰⁺ lzero
zero-ℝ⁰⁺ = nonnegative-real-ℚ⁰⁺ zero-ℚ⁰⁺

one-ℝ⁰⁺ : ℝ⁰⁺ lzero
one-ℝ⁰⁺ = nonnegative-real-ℚ⁰⁺ one-ℚ⁰⁺

one-half-ℝ⁰⁺ : ℝ⁰⁺ lzero
one-half-ℝ⁰⁺ = nonnegative-real-ℚ⁺ one-half-ℚ⁺
```

### A real number is nonnegative if and only if every element of its upper cut is positive

```agda
abstract
  is-positive-is-in-upper-cut-ℝ⁰⁺ :
    {l : Level} → (x : ℝ⁰⁺ l) {q : ℚ} → is-in-upper-cut-ℝ⁰⁺ x q →
    is-positive-ℚ q
  is-positive-is-in-upper-cut-ℝ⁰⁺ (x , 0≤x) x<q =
    is-positive-le-zero-ℚ
      ( reflects-le-real-ℚ
        ( concatenate-leq-le-ℝ zero-ℝ x _
          ( 0≤x)
          ( le-real-is-in-upper-cut-ℝ x x<q)))

abstract opaque
  unfolding leq-ℝ' real-ℚ

  is-nonnegative-is-positive-upper-cut-ℝ :
    {l : Level} → (x : ℝ l) → (upper-cut-ℝ x ⊆ is-positive-prop-ℚ) →
    is-nonnegative-ℝ x
  is-nonnegative-is-positive-upper-cut-ℝ x Uₓ⊆ℚ⁺ =
    leq-leq'-ℝ zero-ℝ x (λ q q∈Uₓ → le-zero-is-positive-ℚ (Uₓ⊆ℚ⁺ q q∈Uₓ))
```

### A real number is nonnegative if and only if every negative rational number is in its lower cut

```agda
abstract opaque
  unfolding leq-ℝ real-ℚ

  is-nonnegative-leq-negative-lower-cut-ℝ :
    {l : Level} (x : ℝ l) → (is-negative-prop-ℚ ⊆ lower-cut-ℝ x) →
    is-nonnegative-ℝ x
  is-nonnegative-leq-negative-lower-cut-ℝ x ℚ⁻⊆Lₓ q q<0 =
    ℚ⁻⊆Lₓ q (is-negative-le-zero-ℚ q<0)

  leq-negative-lower-cut-is-nonnegative-ℝ :
    {l : Level} (x : ℝ l) → is-nonnegative-ℝ x →
    (is-negative-prop-ℚ ⊆ lower-cut-ℝ x)
  leq-negative-lower-cut-is-nonnegative-ℝ x 0≤x q is-neg-q =
    0≤x q (le-zero-is-negative-ℚ is-neg-q)
```

### Every nonnegative real number has a positive rational number in its upper cut

```agda
abstract
  exists-ℚ⁺-in-upper-cut-ℝ⁰⁺ :
    {l : Level} → (x : ℝ⁰⁺ l) →
    exists ℚ⁺ (λ q → upper-cut-ℝ⁰⁺ x (rational-ℚ⁺ q))
  exists-ℚ⁺-in-upper-cut-ℝ⁰⁺ x =
    map-trunc-Prop
      ( λ (q , x<q) → ((q , is-positive-is-in-upper-cut-ℝ⁰⁺ x x<q) , x<q))
      ( is-inhabited-upper-cut-ℝ⁰⁺ x)
```

### Every nonnegative real number is less than some positive rational number

```agda
abstract
  exists-ℚ⁺-le-ℝ⁰⁺ :
    {l : Level} → (x : ℝ⁰⁺ l) →
    exists ℚ⁺ (λ q → le-prop-ℝ (real-ℝ⁰⁺ x) (real-ℚ⁺ q))
  exists-ℚ⁺-le-ℝ⁰⁺ x =
    map-tot-exists
      ( λ _ → le-real-is-in-upper-cut-ℝ (real-ℝ⁰⁺ x))
      ( exists-ℚ⁺-in-upper-cut-ℝ⁰⁺ x)
```

### Nonpositive rational numbers are not less than or equal to nonnegative real numbers

```agda
module _
  {l : Level} (x : ℝ⁰⁺ l) (q : ℚ)
  where

  abstract
    not-le-leq-zero-rational-ℝ⁰⁺ :
      leq-ℚ q zero-ℚ → ¬ (le-ℝ (real-ℝ⁰⁺ x) (real-ℚ q))
    not-le-leq-zero-rational-ℝ⁰⁺ q≤0 x<q =
      irreflexive-le-ℝ
        ( real-ℝ⁰⁺ x)
        ( concatenate-le-leq-ℝ _ _ _
          ( x<q)
          ( transitive-leq-ℝ _ _ _
            ( is-nonnegative-real-ℝ⁰⁺ x)
            ( preserves-leq-real-ℚ q≤0)))
```

### If a nonnegative real number is less than a rational number, the rational number is positive

```agda
module _
  {l : Level} (x : ℝ⁰⁺ l) (q : ℚ)
  where

  abstract
    is-positive-le-nonnegative-real-ℚ :
      le-ℝ (real-ℝ⁰⁺ x) (real-ℚ q) → is-positive-ℚ q
    is-positive-le-nonnegative-real-ℚ x<q =
      is-positive-le-zero-ℚ
        ( reflects-le-real-ℚ
          ( concatenate-leq-le-ℝ _ _ _ (is-nonnegative-real-ℝ⁰⁺ x) x<q))
```

### `x ≤ y` if and only if `y - x` is nonnegative

```agda
module _
  {l1 l2 : Level} {x : ℝ l1} {y : ℝ l2} (H : leq-ℝ x y)
  where

  abstract
    is-nonnegative-diff-leq-ℝ : is-nonnegative-ℝ (y -ℝ x)
    is-nonnegative-diff-leq-ℝ =
      leq-transpose-left-add-ℝ
        ( zero-ℝ)
        ( x)
        ( y)
        ( inv-tr
          ( λ z → leq-ℝ z y)
          ( left-unit-law-add-ℝ x)
          ( H))

  nonnegative-diff-leq-ℝ : ℝ⁰⁺ (l1 ⊔ l2)
  nonnegative-diff-leq-ℝ = (y -ℝ x , is-nonnegative-diff-leq-ℝ)

abstract
  leq-is-nonnegative-diff-ℝ :
    {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2) → is-nonnegative-ℝ (y -ℝ x) →
    leq-ℝ x y
  leq-is-nonnegative-diff-ℝ x y 0≤y-x =
    tr
      ( λ z → leq-ℝ z y)
      ( left-unit-law-add-ℝ x)
      ( leq-transpose-right-diff-ℝ _ _ _ 0≤y-x)
```

### If a nonnegative real number `x` is less than or equal to a real number `y`, `y` is nonnegative

```agda
abstract
  is-nonnegative-leq-ℝ⁰⁺ :
    {l1 l2 : Level} (x : ℝ⁰⁺ l1) (y : ℝ l2) → leq-ℝ (real-ℝ⁰⁺ x) y →
    is-nonnegative-ℝ y
  is-nonnegative-leq-ℝ⁰⁺ (x , 0≤x) y x≤y = transitive-leq-ℝ zero-ℝ x y x≤y 0≤x

  is-nonnegative-le-ℝ⁰⁺ :
    {l1 l2 : Level} (x : ℝ⁰⁺ l1) (y : ℝ l2) → le-ℝ (real-ℝ⁰⁺ x) y →
    is-nonnegative-ℝ y
  is-nonnegative-le-ℝ⁰⁺ x y x<y =
    is-nonnegative-leq-ℝ⁰⁺ x y (leq-le-ℝ x<y)
```

### Nonnegativity is preserved by similarity

```agda
abstract
  is-nonnegative-sim-ℝ :
    {l1 l2 : Level} {x : ℝ l1} {y : ℝ l2} → is-nonnegative-ℝ x → sim-ℝ x y →
    is-nonnegative-ℝ y
  is-nonnegative-sim-ℝ {x = x} {y = y} 0≤x x~y =
    preserves-leq-right-sim-ℝ x~y 0≤x
```

### Raising the universe levels of nonnegative real numbers

```agda
abstract
  is-nonnegative-raise-ℝ :
    {l1 : Level} (l : Level) (x : ℝ l1) →
    is-nonnegative-ℝ x → is-nonnegative-ℝ (raise-ℝ l x)
  is-nonnegative-raise-ℝ l x is-nonneg-x =
    is-nonnegative-sim-ℝ is-nonneg-x (sim-raise-ℝ l x)

raise-ℝ⁰⁺ : {l1 : Level} (l : Level) → ℝ⁰⁺ l1 → ℝ⁰⁺ (l ⊔ l1)
raise-ℝ⁰⁺ l (x , is-nonneg-x) =
  (raise-ℝ l x , is-nonnegative-raise-ℝ l x is-nonneg-x)

raise-zero-ℝ⁰⁺ : (l : Level) → ℝ⁰⁺ l
raise-zero-ℝ⁰⁺ l = raise-ℝ⁰⁺ l zero-ℝ⁰⁺
```
