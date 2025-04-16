# The Archimedean property of the positive integers

```agda
module elementary-number-theory.archimedean-property-positive-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.archimedean-property-natural-numbers
open import elementary-number-theory.difference-integers
open import elementary-number-theory.inequality-integers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonnegative-integers
open import elementary-number-theory.nonzero-natural-numbers
open import elementary-number-theory.positive-and-negative-integers
open import elementary-number-theory.positive-integers
open import elementary-number-theory.strict-inequality-integers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.universe-levels
```

</details>

## Idea

The
{{#concept "Archimedean property" Disambiguation="positive integers" Agda=archimedean-property-ℤ⁺}}
of the [positive integers](elementary-number-theory.positive-integers.md) states
that for any positive integers `x y : ℤ⁺` there is an `n : ℕ` such that
`y < n *ℕ x`.

More precisely, for any positive integers `x y : ℤ⁺, there exists a unique `n :
ℕ`such that`n *ℕ x ≤ y < (n + 1) *ℕ
x`; this is the {{#concept "Archimedean modulus" Agda=center-archimedean-modulus-ℤ⁺}} of `y`with respect to`x`.
All natural numbers greater than the Archimedean modulus are witnesses of the
Archimedean property.

## Definition

### Archimedean modulus of positive integer with respect to a positive integer

```agda
module _
  (x y : ℤ⁺)
  where

  is-archimedean-modulus-prop-ℤ⁺ : ℕ → Prop lzero
  is-archimedean-modulus-prop-ℤ⁺ n =
    product-Prop
      ( leq-ℤ-Prop (int-ℕ n *ℤ int-positive-ℤ x) (int-positive-ℤ y))
      ( le-ℤ-Prop (int-positive-ℤ y) (int-ℕ (succ-ℕ n) *ℤ int-positive-ℤ x))

  is-archimedean-modulus-ℤ⁺ : ℕ → UU lzero
  is-archimedean-modulus-ℤ⁺ n = type-Prop (is-archimedean-modulus-prop-ℤ⁺ n)

  type-archimedean-modulus-ℤ⁺ : UU lzero
  type-archimedean-modulus-ℤ⁺ = type-subtype is-archimedean-modulus-prop-ℤ⁺
```

## Properties

### Archimedean moduli on positive integers are equivalent to Archimedean moduli on the natural numbers

```agda
positive-int-is-archimedean-modulus-ℕ :
  (m n : ℕ) →
  (k : ℕ) →
  is-archimedean-modulus-ℕ (succ-ℕ m) (succ-ℕ n) (is-nonzero-succ-ℕ m) k →
  is-archimedean-modulus-ℤ⁺ (positive-int-ℕ m) (positive-int-ℕ n) k
positive-int-is-archimedean-modulus-ℕ m n k (H , K) =
  binary-tr
    ( leq-ℤ)
    ( ( inv (mul-int-ℕ k (succ-ℕ m))) ∙
      ( ap
        ( mul-ℤ (int-ℕ k))
        ( eq-int-positive-succ-positive-int-ℕ m)))
    ( eq-int-positive-succ-positive-int-ℕ n)
    ( leq-int-ℕ
      ( k *ℕ succ-ℕ m)
      ( succ-ℕ n)
      ( H)) ,
  binary-tr
    ( le-ℤ)
    ( eq-int-positive-succ-positive-int-ℕ n)
    ( ( inv (mul-int-ℕ (succ-ℕ k) (succ-ℕ m))) ∙
      ( ap
        ( mul-ℤ (in-pos-ℤ k))
        ( eq-int-positive-succ-positive-int-ℕ m)))
    ( le-natural-le-ℤ
      ( succ-ℕ n)
      ( succ-ℕ k *ℕ succ-ℕ m)
      ( K))

nat-positive-is-archimedean-modulus-ℤ⁺ :
  (x y : ℤ⁺) →
  (k : ℕ) →
  is-archimedean-modulus-ℤ⁺ x y k →
  is-archimedean-modulus-ℕ
    ( succ-ℕ (nat-positive-ℤ x))
    ( succ-ℕ (nat-positive-ℤ y))
    ( is-nonzero-succ-ℕ (nat-positive-ℤ x))
    ( k)
nat-positive-is-archimedean-modulus-ℤ⁺ x y k (H , K) =
  ( reflects-leq-int-ℕ
    ( k *ℕ succ-ℕ (nat-positive-ℤ x))
    ( succ-ℕ (nat-positive-ℤ y))
    ( binary-tr
      ( leq-ℤ)
      ( ( ap
          ( mul-ℤ (int-ℕ k))
          ( inv (eq-int-positive-succ-nat-positive-ℤ x))) ∙
        ( mul-int-ℕ k (succ-ℕ (nat-positive-ℤ x))))
      ( inv (eq-int-positive-succ-nat-positive-ℤ y))
      ( H))) ,
  ( reflects-le-int-ℕ
    ( succ-ℕ (nat-positive-ℤ y))
    ( succ-ℕ k *ℕ succ-ℕ (nat-positive-ℤ x))
    ( binary-tr
      ( le-ℤ)
      ( inv (eq-int-positive-succ-nat-positive-ℤ y))
      ( ( ap
          ( mul-ℤ (int-ℕ (succ-ℕ k)))
          ( inv (eq-int-positive-succ-nat-positive-ℤ x))) ∙
        ( mul-int-ℕ (succ-ℕ k) (succ-ℕ (nat-positive-ℤ x))))
      ( K)))
```

### All Archimedean moduli between two positive integers are equal

```agda
module _
  (x y : ℤ⁺)
  where

  all-eq-is-archimedean-modulus-ℤ⁺ :
    (m n : ℕ) →
    is-archimedean-modulus-ℤ⁺ x y m →
    is-archimedean-modulus-ℤ⁺ x y n →
    m ＝ n
  all-eq-is-archimedean-modulus-ℤ⁺ m n Hm Hn =
    all-eq-is-archimedean-modulus-ℕ
      ( succ-ℕ (nat-positive-ℤ x))
      ( succ-ℕ (nat-positive-ℤ y))
      ( is-nonzero-succ-ℕ (nat-positive-ℤ x))
      ( m)
      ( n)
      ( nat-positive-is-archimedean-modulus-ℤ⁺ x y m Hm)
      ( nat-positive-is-archimedean-modulus-ℤ⁺ x y n Hn)
```

### The type family of Archimedean moduli is torsorial

```agda
module _
  (x y : ℤ⁺)
  where

  is-prop-archimedean-modulus-ℤ⁺ : is-prop (type-archimedean-modulus-ℤ⁺ x y)
  is-prop-archimedean-modulus-ℤ⁺ =
    is-prop-all-elements-equal
      ( λ u v →
        eq-type-subtype
          ( is-archimedean-modulus-prop-ℤ⁺ x y)
          ( all-eq-is-archimedean-modulus-ℤ⁺
            ( x)
            ( y)
            ( pr1 u)
            ( pr1 v)
            ( pr2 u)
            ( pr2 v)))

  archimedean-modulus-prop-ℤ⁺ : Prop lzero
  archimedean-modulus-prop-ℤ⁺ =
    (type-archimedean-modulus-ℤ⁺ x y , is-prop-archimedean-modulus-ℤ⁺)

  torsorial-archimedean-modulus-ℤ⁺ :
    is-torsorial (is-archimedean-modulus-ℤ⁺ x y)
  torsorial-archimedean-modulus-ℤ⁺ =
    ( binary-tr
      ( type-archimedean-modulus-ℤ⁺)
      ( is-section-nat-positive-ℤ x)
      ( is-section-nat-positive-ℤ y)
      ( tot
        ( positive-int-is-archimedean-modulus-ℕ
          ( nat-positive-ℤ x)
          ( nat-positive-ℤ y))
        ( center-archimedean-modulus-ℕ
          ( succ-ℕ (nat-positive-ℤ x))
          ( succ-ℕ (nat-positive-ℤ y))
          ( is-nonzero-succ-ℕ (nat-positive-ℤ x))))) ,
    ( λ x → eq-is-prop is-prop-archimedean-modulus-ℤ⁺)
```

### The unique Archimedean modulus between two positive integers

```agda
module _
  (x y : ℤ⁺)
  where

  center-archimedean-modulus-ℤ⁺ : type-archimedean-modulus-ℤ⁺ x y
  center-archimedean-modulus-ℤ⁺ =
    center (torsorial-archimedean-modulus-ℤ⁺ x y)

  nat-archimedean-modulus-ℤ⁺ : ℕ
  nat-archimedean-modulus-ℤ⁺ = pr1 center-archimedean-modulus-ℤ⁺

  is-modulus-nat-archimedean-modulus-ℤ⁺ :
    is-archimedean-modulus-ℤ⁺ x y nat-archimedean-modulus-ℤ⁺
  is-modulus-nat-archimedean-modulus-ℤ⁺ = pr2 center-archimedean-modulus-ℤ⁺

  leq-left-nat-archimedean-modulus-ℤ⁺ :
    leq-ℤ
      ( (int-ℕ nat-archimedean-modulus-ℤ⁺) *ℤ (int-positive-ℤ x))
      ( int-positive-ℤ y)
  leq-left-nat-archimedean-modulus-ℤ⁺ =
    pr1 is-modulus-nat-archimedean-modulus-ℤ⁺

  le-right-nat-archimedean-modulus-ℤ⁺ :
    le-ℤ
      ( int-positive-ℤ y)
      ( (int-ℕ (succ-ℕ nat-archimedean-modulus-ℤ⁺)) *ℤ (int-positive-ℤ x))
  le-right-nat-archimedean-modulus-ℤ⁺ =
    pr2 is-modulus-nat-archimedean-modulus-ℤ⁺
```

### The Archimedean property of the positive integers

```agda
abstract
  bound-archimedean-property-ℤ⁺ :
    (x y : ℤ⁺) →
    Σ ℕ (λ n → le-ℤ (int-positive-ℤ y) (int-ℕ n *ℤ int-positive-ℤ x))
  bound-archimedean-property-ℤ⁺ x y =
    ( succ-ℕ (nat-archimedean-modulus-ℤ⁺ x y)) ,
    ( le-right-nat-archimedean-modulus-ℤ⁺ x y)

  archimedean-property-ℤ⁺ :
    (x y : ℤ⁺) →
    exists ℕ (λ n → le-ℤ-Prop (int-positive-ℤ y) (int-ℕ n *ℤ int-positive-ℤ x))
  archimedean-property-ℤ⁺ x y =
    unit-trunc-Prop (bound-archimedean-property-ℤ⁺ x y)
```

## External links

- [Archimedean property](https://en.wikipedia.org/wiki/Archimedean_property) at
  Wikipedia
