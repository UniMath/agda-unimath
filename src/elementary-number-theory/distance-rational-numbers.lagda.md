# The distance between rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.distance-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.absolute-value-rational-numbers
open import elementary-number-theory.addition-nonnegative-rational-numbers
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.additive-group-of-rational-numbers
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.inequality-nonnegative-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.maximum-rational-numbers
open import elementary-number-theory.minimum-rational-numbers
open import elementary-number-theory.multiplication-nonnegative-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.nonnegative-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.transport-along-identifications
```

</details>

## Idea

The
{{#concept "distance function" Disambiguation="between rational numbers" Agda=dist-ℚ}}
between [rational numbers](elementary-number-theory.rational-numbers.md)
measures how far two rational numbers are apart.

```agda
dist-ℚ : ℚ → ℚ → ℚ⁰⁺
dist-ℚ p q = abs-ℚ (p -ℚ q)

rational-dist-ℚ : ℚ → ℚ → ℚ
rational-dist-ℚ p q = rational-ℚ⁰⁺ (dist-ℚ p q)
```

## Properties

### Commutativity

```agda
abstract
  commutative-dist-ℚ : (p q : ℚ) → dist-ℚ p q ＝ dist-ℚ q p
  commutative-dist-ℚ p q =
    inv (abs-neg-ℚ _) ∙ ap abs-ℚ (distributive-neg-diff-ℚ _ _)
```

### A rational number's distance from itself is zero

```agda
abstract
  dist-self-ℚ : (q : ℚ) → dist-ℚ q q ＝ zero-ℚ⁰⁺
  dist-self-ℚ q =
    ap abs-ℚ (right-inverse-law-add-ℚ q) ∙ abs-rational-ℚ⁰⁺ zero-ℚ⁰⁺

  rational-dist-self-ℚ : (q : ℚ) → rational-dist-ℚ q q ＝ zero-ℚ
  rational-dist-self-ℚ q = ap rational-ℚ⁰⁺ (dist-self-ℚ q)
```

### The differences of the arguments are less than or equal to their distance

```agda
abstract
  leq-diff-dist-ℚ : (p q : ℚ) → leq-ℚ (p -ℚ q) (rational-dist-ℚ p q)
  leq-diff-dist-ℚ p q = leq-abs-ℚ (p -ℚ q)

  leq-reversed-diff-dist-ℚ :
    (p q : ℚ) → leq-ℚ (q -ℚ p) (rational-dist-ℚ p q)
  leq-reversed-diff-dist-ℚ p q =
    tr
      ( leq-ℚ (q -ℚ p))
      ( ap rational-ℚ⁰⁺ (commutative-dist-ℚ q p))
      ( leq-diff-dist-ℚ q p)
```

### Zero laws

```agda
opaque
  unfolding neg-ℚ

  right-zero-law-dist-ℚ : (q : ℚ) → dist-ℚ q zero-ℚ ＝ abs-ℚ q
  right-zero-law-dist-ℚ q = ap abs-ℚ (right-unit-law-add-ℚ _)

  left-zero-law-dist-ℚ : (q : ℚ) → dist-ℚ zero-ℚ q ＝ abs-ℚ q
  left-zero-law-dist-ℚ q = commutative-dist-ℚ _ _ ∙ right-zero-law-dist-ℚ q
```

### Distributivity laws

```agda
abstract
  left-distributive-abs-mul-dist-ℚ :
    (p q r : ℚ) →
    abs-ℚ p *ℚ⁰⁺ dist-ℚ q r ＝ dist-ℚ (p *ℚ q) (p *ℚ r)
  left-distributive-abs-mul-dist-ℚ p q r =
    equational-reasoning
      abs-ℚ p *ℚ⁰⁺ dist-ℚ q r
      ＝ abs-ℚ (p *ℚ (q -ℚ r))
        by (inv (abs-mul-ℚ p (q -ℚ r)))
      ＝ dist-ℚ (p *ℚ q) (p *ℚ r)
        by ap abs-ℚ (left-distributive-mul-diff-ℚ p q r)

  right-distributive-abs-mul-dist-ℚ :
    (p q r : ℚ) →
    dist-ℚ q r *ℚ⁰⁺ abs-ℚ p ＝ dist-ℚ (q *ℚ p) (r *ℚ p)
  right-distributive-abs-mul-dist-ℚ p q r =
    equational-reasoning
      dist-ℚ q r *ℚ⁰⁺ abs-ℚ p
      ＝ abs-ℚ p *ℚ⁰⁺ dist-ℚ q r
        by commutative-mul-ℚ⁰⁺ (dist-ℚ q r) (abs-ℚ p)
      ＝ dist-ℚ (p *ℚ q) (p *ℚ r)
        by left-distributive-abs-mul-dist-ℚ p q r
      ＝ dist-ℚ (q *ℚ p) (r *ℚ p)
        by ap-binary dist-ℚ (commutative-mul-ℚ p q) (commutative-mul-ℚ p r)

  left-distributive-mul-dist-ℚ :
    (p : ℚ⁰⁺) (q r : ℚ) →
    p *ℚ⁰⁺ dist-ℚ q r ＝ dist-ℚ (rational-ℚ⁰⁺ p *ℚ q) (rational-ℚ⁰⁺ p *ℚ r)
  left-distributive-mul-dist-ℚ p⁰⁺@(p , _) q r =
    eq-ℚ⁰⁺
      ( equational-reasoning
        p *ℚ rational-dist-ℚ q r
        ＝ rational-abs-ℚ (p *ℚ (q -ℚ r))
          by inv (rational-abs-left-mul-nonnegative-ℚ _ p⁰⁺)
        ＝ rational-abs-ℚ (p *ℚ q +ℚ p *ℚ (neg-ℚ r))
          by ap rational-abs-ℚ (left-distributive-mul-add-ℚ p q (neg-ℚ r))
        ＝ rational-abs-ℚ (p *ℚ q -ℚ p *ℚ r)
          by ap rational-abs-ℚ (ap (p *ℚ q +ℚ_) (right-negative-law-mul-ℚ _ _)))

  right-distributive-mul-dist-ℚ :
    (p : ℚ⁰⁺) (q r : ℚ) →
    dist-ℚ q r *ℚ⁰⁺ p ＝ dist-ℚ (q *ℚ rational-ℚ⁰⁺ p) (r *ℚ rational-ℚ⁰⁺ p)
  right-distributive-mul-dist-ℚ p⁰⁺@(p , _) q r =
    eq-ℚ⁰⁺
      ( equational-reasoning
        rational-dist-ℚ q r *ℚ p
        ＝ p *ℚ rational-dist-ℚ q r by commutative-mul-ℚ _ _
        ＝ rational-dist-ℚ (p *ℚ q) (p *ℚ r)
          by ap rational-ℚ⁰⁺ (left-distributive-mul-dist-ℚ p⁰⁺ q r)
        ＝ rational-dist-ℚ (q *ℚ p) (r *ℚ p)
          by
            ap-binary
              ( rational-dist-ℚ)
              ( commutative-mul-ℚ _ _)
              ( commutative-mul-ℚ _ _))
```

### The distance between two rational numbers is lesser than the sum of their absolute value

```agda
abstract
  leq-dist-add-abs-ℚ : (p q : ℚ) → leq-ℚ⁰⁺ (dist-ℚ p q) (abs-ℚ p +ℚ⁰⁺ abs-ℚ q)
  leq-dist-add-abs-ℚ p q =
    transitive-leq-ℚ
      ( rational-dist-ℚ p q)
      ( (rational-abs-ℚ p) +ℚ (rational-abs-ℚ (neg-ℚ q)))
      ( rational-abs-ℚ p +ℚ rational-abs-ℚ q)
      ( leq-eq-ℚ
        ( (rational-abs-ℚ p) +ℚ (rational-abs-ℚ (neg-ℚ q)))
        ( rational-abs-ℚ p +ℚ rational-abs-ℚ q)
        ( ap (add-ℚ (rational-abs-ℚ p) ∘ rational-ℚ⁰⁺) (abs-neg-ℚ q)))
      ( triangle-inequality-abs-ℚ p (neg-ℚ q))
```

### Triangle inequality

```agda
abstract
  triangle-inequality-dist-ℚ :
    (p q r : ℚ) → leq-ℚ⁰⁺ (dist-ℚ p r) (dist-ℚ p q +ℚ⁰⁺ dist-ℚ q r)
  triangle-inequality-dist-ℚ p q r =
    tr
      ( λ s → leq-ℚ⁰⁺ s (dist-ℚ p q +ℚ⁰⁺ dist-ℚ q r))
      ( ap abs-ℚ
        ( inv (associative-add-ℚ _ _ (neg-ℚ r)) ∙
          ap (_-ℚ r) (is-section-diff-ℚ _ _)))
      ( triangle-inequality-abs-ℚ (p -ℚ q) (q -ℚ r))
```

### Bounding the distance between rational numbers

```agda
abstract
  leq-dist-leq-diff-ℚ :
    (p q r : ℚ) → leq-ℚ (p -ℚ q) r → leq-ℚ (q -ℚ p) r →
    leq-ℚ (rational-dist-ℚ p q) r
  leq-dist-leq-diff-ℚ p q r p-q≤r q-p≤r =
    leq-abs-leq-leq-neg-ℚ
      ( p -ℚ q)
      ( r)
      ( p-q≤r)
      ( inv-tr (λ s → leq-ℚ s r) (distributive-neg-diff-ℚ p q) q-p≤r)

  le-dist-le-diff-ℚ :
    (p q r : ℚ) → le-ℚ (p -ℚ q) r → le-ℚ (q -ℚ p) r →
    le-ℚ (rational-dist-ℚ p q) r
  le-dist-le-diff-ℚ p q r p-q<r q-p<r =
    le-abs-le-le-neg-ℚ
      ( p -ℚ q)
      ( r)
      ( p-q<r)
      ( inv-tr (λ s → le-ℚ s r) (distributive-neg-diff-ℚ p q) q-p<r)
```

### The distance between two rational numbers is the difference of their maximum and minimum

```agda
abstract
  eq-dist-diff-leq-ℚ : (p q : ℚ) → leq-ℚ p q → rational-dist-ℚ p q ＝ q -ℚ p
  eq-dist-diff-leq-ℚ p q p≤q =
    equational-reasoning
      rational-dist-ℚ p q
      ＝ rational-dist-ℚ q p by ap rational-ℚ⁰⁺ (commutative-dist-ℚ p q)
      ＝ q -ℚ p
        by
          rational-abs-zero-leq-ℚ
            ( q -ℚ p)
            ( backward-implication (iff-translate-diff-leq-zero-ℚ p q) p≤q)

  eq-dist-diff-leq-ℚ' : (p q : ℚ) → leq-ℚ q p → rational-dist-ℚ p q ＝ p -ℚ q
  eq-dist-diff-leq-ℚ' p q q≤p =
    ap rational-ℚ⁰⁺ (commutative-dist-ℚ _ _) ∙
    eq-dist-diff-leq-ℚ q p q≤p

  eq-dist-diff-max-min-ℚ :
    (p q : ℚ) → rational-dist-ℚ p q ＝ max-ℚ p q -ℚ min-ℚ p q
  eq-dist-diff-max-min-ℚ p q =
    rec-coproduct
      ( λ p≤q →
        equational-reasoning
          rational-dist-ℚ p q
          ＝ q -ℚ p by eq-dist-diff-leq-ℚ p q p≤q
          ＝ max-ℚ p q -ℚ min-ℚ p q
            by
              inv
                ( ap-diff-ℚ
                  ( left-leq-right-max-ℚ p q p≤q)
                  ( left-leq-right-min-ℚ p q p≤q)))
      ( λ q≤p →
        equational-reasoning
          rational-dist-ℚ p q
          ＝ rational-dist-ℚ q p by ap rational-ℚ⁰⁺ (commutative-dist-ℚ p q)
          ＝ p -ℚ q by eq-dist-diff-leq-ℚ q p q≤p
          ＝ max-ℚ p q -ℚ min-ℚ p q
            by
              inv
                ( ap-diff-ℚ
                  ( right-leq-left-max-ℚ p q q≤p)
                  ( right-leq-left-min-ℚ p q q≤p)))
      ( linear-leq-ℚ p q)
```
