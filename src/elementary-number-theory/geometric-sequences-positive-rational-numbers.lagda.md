# Geometric sequences of positive rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.geometric-sequences-positive-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.additive-group-of-rational-numbers
open import elementary-number-theory.arithmetic-sequences-positive-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.multiplicative-group-of-positive-rational-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.sequences
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.powers-of-elements-monoids
```

</details>

## Idea

The
{{#concept "geometric sequence" Disambiguation="of positive rational numbers" Agda=geometric-sequence-ℚ⁺ WD="geometric progression" WDID=Q173523}}
of positive rational numbers with initial term `(a : ℚ⁺)` and common ratio
`(r : ℚ⁺)` is the sequence `u : ℕ → ℚ⁺` characterized by

- `u₀ = a`
- `∀ (n : ℕ) uₙ₊₁ = uₙ r`.

## Definitions

### Preliminary definition

```agda
module _
  (r : ℚ⁺)
  where

  power-mul-ℚ⁺ : sequence ℚ⁺
  power-mul-ℚ⁺ n = power-Monoid monoid-mul-ℚ⁺ n r
```

### Geometric sequences of positive rational numbers

```agda
module _
  (a r : ℚ⁺)
  where

  geometric-sequence-ℚ⁺ : sequence ℚ⁺
  geometric-sequence-ℚ⁺ = mul-ℚ⁺ a ∘ power-mul-ℚ⁺ r
```

### Unitary arithmetic sequences of rational numbers

A geometric sequence with initial term equal to `1` is called unitary

```agda
module _
  (r : ℚ⁺)
  where

  unitary-geometric-sequence-ℚ⁺ : sequence ℚ⁺
  unitary-geometric-sequence-ℚ⁺ = geometric-sequence-ℚ⁺ one-ℚ⁺ r
```

## Properties

### `u₀ = a`

```agda
module _
  (a d : ℚ⁺)
  where

  abstract
    eq-init-geometric-sequence-ℚ⁺ :
      geometric-sequence-ℚ⁺ a d zero-ℕ ＝ a
    eq-init-geometric-sequence-ℚ⁺ = right-unit-law-mul-ℚ⁺ a
```

### `uₙ₊₁ = uₙ r`

```agda
module _
  (a r : ℚ⁺)
  where

  abstract
    eq-succ-geometric-sequence-ℚ⁺ :
      ( n : ℕ) →
      ( geometric-sequence-ℚ⁺ a r (succ-ℕ n)) ＝
      ( geometric-sequence-ℚ⁺ a r n *ℚ⁺ r)
    eq-succ-geometric-sequence-ℚ⁺ n =
      ( ap
        ( mul-ℚ⁺ a)
        ( power-succ-Monoid monoid-mul-ℚ⁺ n r)) ∙
      ( inv
        (associative-mul-ℚ⁺
          ( a)
          ( power-mul-ℚ⁺ r n)
          ( r)))
```

### The nth term of a geometric sequence with initial term `a` and common ratio `r` is `a rⁿ`

```agda
module _
  (a r : ℚ⁺) (n : ℕ)
  where

  abstract
    compute-geometric-sequence-ℚ⁺ :
      ( a *ℚ⁺ power-mul-ℚ⁺ r n) ＝
      ( geometric-sequence-ℚ⁺ a r n)
    compute-geometric-sequence-ℚ⁺ = refl
```

### The pointwise inverse of the unitary geometric sequence with common ratio `r` is the unitary geometric sequence with common ratio `1/r`

```agda
module _
  (r : ℚ⁺)
  where

  abstract
    eq-inv-unitary-geometric-sequence-ℚ⁺ :
      (n : ℕ) →
      unitary-geometric-sequence-ℚ⁺ (inv-ℚ⁺ r) n ＝
      inv-ℚ⁺ (unitary-geometric-sequence-ℚ⁺ r n)
    eq-inv-unitary-geometric-sequence-ℚ⁺ zero-ℕ =
      eq-init-geometric-sequence-ℚ⁺ one-ℚ⁺ (inv-ℚ⁺ r) ∙
      inv-tr
        ( Id one-ℚ⁺ ∘ inv-ℚ⁺)
        ( eq-init-geometric-sequence-ℚ⁺ one-ℚ⁺ r)
        ( inv inv-one-ℚ⁺)
    eq-inv-unitary-geometric-sequence-ℚ⁺ (succ-ℕ n) =
      ( eq-succ-geometric-sequence-ℚ⁺ one-ℚ⁺ (inv-ℚ⁺ r) n) ∙
      ( ap (λ x → x *ℚ⁺ inv-ℚ⁺ r) (eq-inv-unitary-geometric-sequence-ℚ⁺ n)) ∙
      ( inv (inv-mul-ℚ⁺ (unitary-geometric-sequence-ℚ⁺ r n) r)) ∙
      ( ap inv-ℚ⁺ (inv (eq-succ-geometric-sequence-ℚ⁺ one-ℚ⁺ r n)))
```

### Linear-exponential inequality / Bernoulli's inequality

The unitary arithmetic sequence with common difference `d` is lesser than the
unitary geometric sequence with common ratio `1 + d`: `1 + n d ≤ (1 + d)ⁿ`.

```agda
module _
  (d : ℚ⁺)
  where

  abstract
    linear-exponential-inequality-ℚ⁺ :
      (n : ℕ) →
      leq-ℚ⁺
        ( unitary-arithmetic-sequence-ℚ⁺ d n)
        ( unitary-geometric-sequence-ℚ⁺ (one-ℚ⁺ +ℚ⁺ d) n)
    linear-exponential-inequality-ℚ⁺ zero-ℕ =
      binary-tr
        ( leq-ℚ⁺)
        ( inv (eq-init-arithmetic-sequence-ℚ⁺ one-ℚ⁺ d))
        ( inv (eq-init-geometric-sequence-ℚ⁺ one-ℚ⁺ (one-ℚ⁺ +ℚ⁺ d)))
        ( refl-leq-ℚ one-ℚ)
    linear-exponential-inequality-ℚ⁺ (succ-ℕ n) =
      transitive-leq-ℚ
        ( rational-ℚ⁺ (unitary-arithmetic-sequence-ℚ⁺ d (succ-ℕ n)))
        ( rational-ℚ⁺
          ( mul-ℚ⁺
            ( unitary-arithmetic-sequence-ℚ⁺ d n)
            ( one-ℚ⁺ +ℚ⁺ d)))
        ( rational-ℚ⁺ (unitary-geometric-sequence-ℚ⁺ (one-ℚ⁺ +ℚ⁺ d) (succ-ℕ n)))
        ( inv-tr
          ( leq-ℚ⁺ (unitary-arithmetic-sequence-ℚ⁺ d n *ℚ⁺ (one-ℚ⁺ +ℚ⁺ d)))
          ( eq-succ-geometric-sequence-ℚ⁺ one-ℚ⁺ (one-ℚ⁺ +ℚ⁺ d) n)
          ( preserves-leq-right-mul-ℚ⁺
            ( one-ℚ⁺ +ℚ⁺ d)
            ( rational-ℚ⁺ (unitary-arithmetic-sequence-ℚ⁺ d n))
            ( rational-ℚ⁺ (unitary-geometric-sequence-ℚ⁺ (one-ℚ⁺ +ℚ⁺ d) n))
            ( linear-exponential-inequality-ℚ⁺ n)))
        ( bounded-ratio-unitary-arithmetic-sequence-ℚ⁺ d n)
```

### Asymptotical behaviour of unitary geometric sequences of positive rational numbers

#### A unitary geometric sequence with common ratio `r > 1` is unbounded

```agda
module _
  (r : ℚ⁺) (H : le-ℚ⁺ one-ℚ⁺ r)
  where

  is-unbounded-geometric-sequence-ℚ⁺ :
    (M : ℚ⁺) → Σ ℕ (le-ℚ⁺ M ∘ unitary-geometric-sequence-ℚ⁺ r)
  is-unbounded-geometric-sequence-ℚ⁺ M =
    tot
      ( tr-linear-exponential-bound)
      ( is-unbounded-arithmetic-sequence-ℚ⁺ one-ℚ⁺ d M)
    where

      d : ℚ⁺
      d = le-diff-ℚ⁺ one-ℚ⁺ r H

      tr-linear-exponential-bound :
        (n : ℕ) (I : le-ℚ⁺ M (unitary-arithmetic-sequence-ℚ⁺ d n)) →
        le-ℚ⁺ M (unitary-geometric-sequence-ℚ⁺ r n)
      tr-linear-exponential-bound n I =
        concatenate-le-leq-ℚ
          ( rational-ℚ⁺ M)
          ( rational-ℚ⁺ (unitary-arithmetic-sequence-ℚ⁺ d n))
          ( rational-ℚ⁺ (unitary-geometric-sequence-ℚ⁺ r n))
          ( I)
          ( tr
            ( λ x →
              leq-ℚ⁺
                ( unitary-arithmetic-sequence-ℚ⁺ d n)
                ( unitary-geometric-sequence-ℚ⁺ x n))
            ( right-diff-law-add-ℚ⁺ one-ℚ⁺ r H)
            ( linear-exponential-inequality-ℚ⁺ d n))
```

#### A unitary geometric sequence with common ratio `r = 1` is constant

```agda
abstract
  is-constant-geometric-sequence-ℚ⁺ :
    (n : ℕ) → unitary-geometric-sequence-ℚ⁺ one-ℚ⁺ n ＝ one-ℚ⁺
  is-constant-geometric-sequence-ℚ⁺ zero-ℕ =
    eq-init-geometric-sequence-ℚ⁺ one-ℚ⁺ one-ℚ⁺
  is-constant-geometric-sequence-ℚ⁺ (succ-ℕ n) =
    ( eq-succ-geometric-sequence-ℚ⁺ one-ℚ⁺ one-ℚ⁺ n) ∙
    ( right-unit-law-mul-ℚ⁺ (unitary-geometric-sequence-ℚ⁺ one-ℚ⁺ n)) ∙
    ( is-constant-geometric-sequence-ℚ⁺ n)
```

#### A unitary geometric sequence with common ratio `r < 1` gets arbitrarily small

```agda
module _
  (r : ℚ⁺) (H : le-ℚ⁺ r one-ℚ⁺)
  where

  is-arbitrarily-small-geometric-sequence-ℚ⁺ :
    (ε : ℚ⁺) → Σ ℕ (λ n → le-ℚ⁺ (unitary-geometric-sequence-ℚ⁺ r n) ε)
  is-arbitrarily-small-geometric-sequence-ℚ⁺ ε =
    tot
      ( inv-bound)
      ( is-unbounded-geometric-sequence-ℚ⁺
        ( inv-ℚ⁺ r)
        ( inv-le-ℚ⁺
          ( inv-ℚ⁺ r)
          ( one-ℚ⁺)
            ( binary-tr
              ( le-ℚ⁺)
              ( inv (inv-inv-ℚ⁺ r))
              ( inv (inv-one-ℚ⁺))
              ( H)))
        ( inv-ℚ⁺ ε))
    where

      inv-bound :
        (n : ℕ)
        (I : le-ℚ⁺ (inv-ℚ⁺ ε) (unitary-geometric-sequence-ℚ⁺ (inv-ℚ⁺ r) n)) →
        le-ℚ⁺ (unitary-geometric-sequence-ℚ⁺ r n) ε
      inv-bound n I =
        inv-le-ℚ⁺
          ( ε)
          ( unitary-geometric-sequence-ℚ⁺ r n)
          ( tr
            ( le-ℚ⁺ (inv-ℚ⁺ ε))
            ( eq-inv-unitary-geometric-sequence-ℚ⁺ r n)
            ( I))
```

## References

- [Geometric progressions](https://en.wikipedia.org/wiki/Geometric_progression)
  at Wikipedia
- [Bernoulli's inequality](https://en.wikipedia.org/wiki/Bernoulli%27s_inequality)
  at Wikipedia
