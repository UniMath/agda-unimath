# Rational MacNeille real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.rational-macneille-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.integers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonnegative-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers
open import elementary-number-theory.unit-fractions-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.logical-equivalences
open import foundation.negated-equality
open import foundation.negation
open import foundation.propositions
open import foundation.retractions
open import foundation.sections
open import foundation.sets
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-lower-dedekind-real-numbers
open import real-numbers.inequality-macneille-real-numbers
open import real-numbers.located-macneille-real-numbers
open import real-numbers.lower-dedekind-real-numbers
open import real-numbers.macneille-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-lower-dedekind-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-macneille-real-numbers
```

</details>

## Idea

The type of [rationals](elementary-number-theory.rational-numbers.md) `ℚ` embeds
into the type of [MacNeille reals](real-numbers.macneille-real-numbers.md). We
call numbers in the image of this embedding
{{#concept "rational MacNeille real numbers" Agda=rational-macneille-ℝ}}.

## Definitions

### The inclusion of `ℚ` into MacNeille reals

```agda
macneille-real-ℚ : ℚ → macneille-ℝ lzero
macneille-real-ℚ q = pr1 (located-macneille-real-ℚ q)

macneille-real-ℚ⁺ : ℚ⁺ → macneille-ℝ lzero
macneille-real-ℚ⁺ q =
  macneille-real-ℚ (rational-ℚ⁺ q)

macneille-real-ℚ⁰⁺ : ℚ⁰⁺ → macneille-ℝ lzero
macneille-real-ℚ⁰⁺ q =
  macneille-real-ℚ (rational-ℚ⁰⁺ q)

abstract opaque
  unfolding real-ℚ

  eq-lower-real-macneille-real-ℚ :
    (q : ℚ) → lower-real-macneille-ℝ (macneille-real-ℚ q) ＝ lower-real-ℚ q
  eq-lower-real-macneille-real-ℚ q = refl
```

### The inclusion of `ℤ` into MacNeille reals

```agda
macneille-real-ℤ : ℤ → macneille-ℝ lzero
macneille-real-ℤ x = macneille-real-ℚ (rational-ℤ x)
```

### The inclusion of `ℕ` into MacNeille reals

```agda
macneille-real-ℕ : ℕ → macneille-ℝ lzero
macneille-real-ℕ n = macneille-real-ℤ (int-ℕ n)
```

### Zero, one, and basic rationals as MacNeille reals

```agda
zero-macneille-ℝ : macneille-ℝ lzero
zero-macneille-ℝ = macneille-real-ℚ zero-ℚ

one-macneille-ℝ : macneille-ℝ lzero
one-macneille-ℝ = macneille-real-ℚ one-ℚ

neg-one-macneille-ℝ : macneille-ℝ lzero
neg-one-macneille-ℝ = macneille-real-ℚ neg-one-ℚ

one-half-macneille-ℝ : macneille-ℝ lzero
one-half-macneille-ℝ = macneille-real-ℚ one-half-ℚ
```

### Raising universe levels of rational MacNeille reals

```agda
raise-macneille-real-ℚ : (l : Level) → ℚ → macneille-ℝ l
raise-macneille-real-ℚ l q =
  macneille-real-ℝ (raise-real-ℚ l q)

raise-zero-macneille-ℝ : (l : Level) → macneille-ℝ l
raise-zero-macneille-ℝ l = raise-macneille-real-ℚ l zero-ℚ

raise-one-macneille-ℝ : (l : Level) → macneille-ℝ l
raise-one-macneille-ℝ l = raise-macneille-real-ℚ l one-ℚ
```

### The property of being a rational MacNeille real number

```agda
module _
  {l : Level} (x : macneille-ℝ l) (p : ℚ)
  where

  is-rational-prop-macneille-ℝ : Prop (lsuc l)
  is-rational-prop-macneille-ℝ =
    ( x ＝ raise-macneille-real-ℚ l p ,
      is-set-macneille-ℝ x (raise-macneille-real-ℚ l p))

  is-rational-macneille-ℝ : UU (lsuc l)
  is-rational-macneille-ℝ = type-Prop is-rational-prop-macneille-ℝ
```

```agda
abstract
  is-emb-raise-macneille-real-ℚ :
    {l : Level} → is-emb (raise-macneille-real-ℚ l)
  is-emb-raise-macneille-real-ℚ {l} =
    is-emb-comp _ _ is-emb-macneille-real-ℝ is-emb-raise-real-ℚ

abstract
  is-injective-raise-macneille-real-ℚ :
    {l : Level} → is-injective (raise-macneille-real-ℚ l)
  is-injective-raise-macneille-real-ℚ {l} =
    is-injective-is-emb is-emb-raise-macneille-real-ℚ

abstract
  all-eq-is-rational-macneille-ℝ :
    {l : Level} (x : macneille-ℝ l) (p q : ℚ) →
    is-rational-macneille-ℝ x p →
    is-rational-macneille-ℝ x q →
    p ＝ q
  all-eq-is-rational-macneille-ℝ x p q H H' =
    is-injective-raise-macneille-real-ℚ (inv H ∙ H')

abstract
  is-prop-is-rational-macneille-ℝ :
    {l : Level} (x : macneille-ℝ l) →
    is-prop (Σ ℚ (is-rational-macneille-ℝ x))
  is-prop-is-rational-macneille-ℝ x =
    is-prop-all-elements-equal
      ( λ p q →
        eq-type-subtype
          ( is-rational-prop-macneille-ℝ x)
          ( all-eq-is-rational-macneille-ℝ
            ( x) (pr1 p) (pr1 q) (pr2 p) (pr2 q)))
```

### The subtype of rational MacNeille reals

```agda
subtype-rational-macneille-ℝ :
  {l : Level} → macneille-ℝ l → Prop (lsuc l)
subtype-rational-macneille-ℝ x =
  (Σ ℚ (is-rational-macneille-ℝ x) , is-prop-is-rational-macneille-ℝ x)

rational-macneille-ℝ : (l : Level) → UU (lsuc l)
rational-macneille-ℝ l = type-subtype subtype-rational-macneille-ℝ

module _
  {l : Level} (x : rational-macneille-ℝ l)
  where

  macneille-rational-macneille-ℝ : macneille-ℝ l
  macneille-rational-macneille-ℝ = pr1 x

  rational-rational-macneille-ℝ : ℚ
  rational-rational-macneille-ℝ = pr1 (pr2 x)

  is-rational-rational-macneille-ℝ :
    is-rational-macneille-ℝ
      macneille-rational-macneille-ℝ
      rational-rational-macneille-ℝ
  is-rational-rational-macneille-ℝ = pr2 (pr2 x)
```

## Properties

### The inclusions are embeddings

```agda
abstract
  is-emb-macneille-real-ℚ : is-emb macneille-real-ℚ
  is-emb-macneille-real-ℚ =
    is-emb-comp _ _ is-emb-macneille-real-ℝ is-emb-real-ℚ

abstract
  is-emb-macneille-real-ℚ⁺ : is-emb macneille-real-ℚ⁺
  is-emb-macneille-real-ℚ⁺ =
    is-emb-comp _ _ is-emb-macneille-real-ℚ is-emb-rational-ℚ⁺

  is-emb-macneille-real-ℚ⁰⁺ : is-emb macneille-real-ℚ⁰⁺
  is-emb-macneille-real-ℚ⁰⁺ =
    is-emb-comp _ _ is-emb-macneille-real-ℚ is-emb-rational-ℚ⁰⁺

  is-emb-macneille-real-ℤ : is-emb macneille-real-ℤ
  is-emb-macneille-real-ℤ =
    is-emb-comp _ _ is-emb-macneille-real-ℚ is-emb-rational-ℤ

  is-emb-macneille-real-ℕ : is-emb macneille-real-ℕ
  is-emb-macneille-real-ℕ =
    is-emb-comp _ _ is-emb-macneille-real-ℤ is-emb-int-ℕ

  is-injective-macneille-real-ℚ : is-injective macneille-real-ℚ
  is-injective-macneille-real-ℚ =
    is-injective-is-emb is-emb-macneille-real-ℚ

  is-injective-macneille-real-ℚ⁺ : is-injective macneille-real-ℚ⁺
  is-injective-macneille-real-ℚ⁺ =
    is-injective-is-emb is-emb-macneille-real-ℚ⁺

  is-injective-macneille-real-ℚ⁰⁺ : is-injective macneille-real-ℚ⁰⁺
  is-injective-macneille-real-ℚ⁰⁺ =
    is-injective-is-emb is-emb-macneille-real-ℚ⁰⁺

  is-injective-macneille-real-ℤ : is-injective macneille-real-ℤ
  is-injective-macneille-real-ℤ =
    is-injective-is-emb is-emb-macneille-real-ℤ

  is-injective-macneille-real-ℕ : is-injective macneille-real-ℕ
  is-injective-macneille-real-ℕ =
    is-injective-is-emb is-emb-macneille-real-ℕ
```

### The embedding of a rational number is rational

```agda
abstract
  is-rational-macneille-real-ℚ :
    (p : ℚ) → is-rational-macneille-ℝ (macneille-real-ℚ p) p
  is-rational-macneille-real-ℚ p =
    ap macneille-real-ℝ (eq-raise-ℝ (real-ℚ p))
```

### The inclusion of rationals into MacNeille reals preserves inequality

```agda
abstract
  leq-macneille-real-ℚ :
    {p q : ℚ} →
    leq-ℚ p q →
    leq-macneille-ℝ
      ( macneille-real-ℚ p)
      ( macneille-real-ℚ q)
  leq-macneille-real-ℚ {p} {q} p≤q =
    leq-macneille-leq-lower-real-macneille-ℝ
      ( macneille-real-ℚ p)
      ( macneille-real-ℚ q)
      ( λ r r<p →
        tr
          ( λ Lq → is-in-cut-lower-ℝ Lq r)
          ( inv (eq-lower-real-macneille-real-ℚ q))
          ( preserves-leq-lower-real-ℚ p q p≤q r
            ( tr
              ( λ Lp → is-in-cut-lower-ℝ Lp r)
              ( eq-lower-real-macneille-real-ℚ p)
              ( r<p))))
```

### A raised rational MacNeille real is rational

```agda
abstract
  is-rational-raise-macneille-real-ℚ :
    (l : Level) (p : ℚ) →
    is-rational-macneille-ℝ (raise-macneille-real-ℚ l p) p
  is-rational-raise-macneille-real-ℚ l p = refl
```

### Rational MacNeille reals are embedded rationals

```agda
abstract
  eq-raise-rational-is-rational-macneille-ℝ :
    {l : Level} {x : macneille-ℝ l} {q : ℚ} →
    is-rational-macneille-ℝ x q → x ＝ raise-macneille-real-ℚ l q
  eq-raise-rational-is-rational-macneille-ℝ {l} {x} {q} H = H

  is-rational-eq-raise-macneille-real-ℚ :
    {l : Level} {x : macneille-ℝ l} {q : ℚ} →
    x ＝ raise-macneille-real-ℚ l q →
    is-rational-macneille-ℝ x q
  is-rational-eq-raise-macneille-real-ℚ {l} {x} {q} x=q = x=q

is-rational-iff-eq-raise-macneille-real-ℚ :
  {l : Level} {x : macneille-ℝ l} {q : ℚ} →
  (is-rational-macneille-ℝ x q) ↔ (x ＝ raise-macneille-real-ℚ l q)
is-rational-iff-eq-raise-macneille-real-ℚ =
  ( eq-raise-rational-is-rational-macneille-ℝ ,
    is-rational-eq-raise-macneille-real-ℚ)
```

### The inclusion of rationals into rational MacNeille reals

```agda
rational-macneille-real-ℚ : ℚ → rational-macneille-ℝ lzero
rational-macneille-real-ℚ q =
  ( macneille-real-ℚ q , q , is-rational-macneille-real-ℚ q)

raise-rational-macneille-real-ℚ :
  (l : Level) → ℚ → rational-macneille-ℝ l
raise-rational-macneille-real-ℚ l q =
  ( raise-macneille-real-ℚ l q , q ,
    is-rational-raise-macneille-real-ℚ l q)
```

### The rationals and rational MacNeille reals are equivalent

```agda
abstract
  is-section-rational-macneille-real-ℚ :
    (q : ℚ) →
    rational-rational-macneille-ℝ (rational-macneille-real-ℚ q) ＝ q
  is-section-rational-macneille-real-ℚ q = refl

  is-retraction-rational-macneille-real-ℚ :
    (x : rational-macneille-ℝ lzero) →
    rational-macneille-real-ℚ (rational-rational-macneille-ℝ x) ＝ x
  is-retraction-rational-macneille-real-ℚ (x , q , H) =
    eq-type-subtype
      subtype-rational-macneille-ℝ
        ( is-rational-macneille-real-ℚ q ∙ inv H)

equiv-rational-macneille-ℝ : rational-macneille-ℝ lzero ≃ ℚ
equiv-rational-macneille-ℝ =
  ( rational-rational-macneille-ℝ ,
    is-equiv-is-invertible
      ( rational-macneille-real-ℚ)
      ( is-section-rational-macneille-real-ℚ)
      ( is-retraction-rational-macneille-real-ℚ))
```

### `0 ≠ 1`

```agda
abstract
  neq-zero-one-macneille-ℝ : zero-macneille-ℝ ≠ one-macneille-ℝ
  neq-zero-one-macneille-ℝ = neq-zero-one-ℚ ∘ is-injective-macneille-real-ℚ

  neq-raise-zero-one-macneille-ℝ :
    (l : Level) → raise-zero-macneille-ℝ l ≠ raise-one-macneille-ℝ l
  neq-raise-zero-one-macneille-ℝ l 0=1ℝ =
    neq-zero-one-ℚ (is-injective-raise-macneille-real-ℚ 0=1ℝ)
```
