# The mediant fraction of two integer fractions

```agda
module elementary-number-theory.mediant-integer-fractions where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers
open import elementary-number-theory.addition-positive-and-negative-integers
open import elementary-number-theory.cross-multiplication-difference-integer-fractions
open import elementary-number-theory.difference-integers
open import elementary-number-theory.divisibility-integers
open import elementary-number-theory.greatest-common-divisor-integers
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.negative-integers
open import elementary-number-theory.positive-and-negative-integers
open import elementary-number-theory.reduced-integer-fractions

open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.identity-types
open import foundation.transport-along-identifications
```

</details>

## Idea

The
{{#concept "mediant" Disambiguation="integer fractions" Agda=mediant-fraction-ℤ}}
of two fractions is the quotient of the sum of the numerators by the sum of the
denominators.

## Definitions

### The mediant of two fractions

```agda
mediant-fraction-ℤ : fraction-ℤ → fraction-ℤ → fraction-ℤ
mediant-fraction-ℤ (a , b) (c , d) = (add-ℤ a c , add-positive-ℤ b d)
```

## Properties

### The mediant preserves the cross-multiplication difference

```agda
cross-mul-diff-left-mediant-fraction-ℤ :
  (x y : fraction-ℤ) →
  cross-mul-diff-fraction-ℤ x y ＝
  cross-mul-diff-fraction-ℤ x ( mediant-fraction-ℤ x y)
cross-mul-diff-left-mediant-fraction-ℤ (nx , dx , px) (ny , dy , py) =
  equational-reasoning
  (ny *ℤ dx -ℤ nx *ℤ dy)
  ＝ (nx *ℤ dx +ℤ ny *ℤ dx) -ℤ (nx *ℤ dx +ℤ nx *ℤ dy)
    by inv
      ( left-translation-diff-ℤ
        ( mul-ℤ ny dx)
        ( mul-ℤ nx dy)
        ( mul-ℤ nx dx))
  ＝ (nx +ℤ ny) *ℤ dx -ℤ nx *ℤ (dx +ℤ dy)
    by ap-diff-ℤ
      ( inv (right-distributive-mul-add-ℤ nx ny dx))
      ( inv (left-distributive-mul-add-ℤ nx dx dy))

cross-mul-diff-right-mediant-fraction-ℤ :
  (x y : fraction-ℤ) →
  cross-mul-diff-fraction-ℤ x y ＝
  cross-mul-diff-fraction-ℤ (mediant-fraction-ℤ x y) y
cross-mul-diff-right-mediant-fraction-ℤ (nx , dx , px) (ny , dy , py) =
  equational-reasoning
  (ny *ℤ dx -ℤ nx *ℤ dy)
  ＝ (ny *ℤ dx +ℤ ny *ℤ dy) -ℤ (nx *ℤ dy +ℤ ny *ℤ dy)
    by inv
      ( right-translation-diff-ℤ
        ( mul-ℤ ny dx)
        ( mul-ℤ nx dy)
        ( mul-ℤ ny dy))
  ＝ ny *ℤ (dx +ℤ dy) -ℤ (nx +ℤ ny) *ℤ dy
    by ap-diff-ℤ
      ( inv (left-distributive-mul-add-ℤ ny dx dy))
      ( inv (right-distributive-mul-add-ℤ nx ny dy))
```

### Common divisors of the numerator and denominator of the mediant of two integer fractions divide their cross-multiplication difference

```agda
div-cross-mul-diff-common-divisor-mediant-fraction-ℤ :
  (x y : fraction-ℤ) →
  (k : ℤ) →
  is-common-divisor-ℤ
    ( numerator-fraction-ℤ (mediant-fraction-ℤ x y))
    ( denominator-fraction-ℤ (mediant-fraction-ℤ x y))
    ( k) →
  div-ℤ k (cross-mul-diff-fraction-ℤ x y)
div-cross-mul-diff-common-divisor-mediant-fraction-ℤ
  x@(nx , dx , _) y@(ny , dy , _) k (div-N , div-D) =
  inv-tr
    ( div-ℤ k)
    ( cross-mul-diff-left-mediant-fraction-ℤ x y)
    ( div-add-ℤ
      ( k)
      ( (nx +ℤ ny) *ℤ dx)
      ( neg-ℤ (nx *ℤ (dx +ℤ dy)))
      ( inv-tr
        ( div-ℤ k)
        ( commutative-mul-ℤ (nx +ℤ ny) dx)
        ( div-mul-ℤ dx k (nx +ℤ ny) div-N))
      ( div-neg-ℤ
        ( k)
        ( nx *ℤ (dx +ℤ dy))
        ( div-mul-ℤ
          ( nx)
          ( k)
          ( dx +ℤ dy)
          ( div-D))))
```

### If the cross-multiplication difference of two fractions is 1 their mediant integer fraction is reduced

```agda
is-reduced-mediant-is-one-cross-mul-diff-fraction-ℤ :
  (x y : fraction-ℤ) →
  is-one-ℤ (cross-mul-diff-fraction-ℤ x y) →
  is-reduced-fraction-ℤ (mediant-fraction-ℤ x y)
is-reduced-mediant-is-one-cross-mul-diff-fraction-ℤ x y H =
  let
    n = numerator-fraction-ℤ (mediant-fraction-ℤ x y)
    d = denominator-fraction-ℤ (mediant-fraction-ℤ x y)

    is-unit-gcd-mediant : is-unit-ℤ (gcd-ℤ n d)
    is-unit-gcd-mediant =
      tr
        ( div-ℤ (gcd-ℤ n d))
        ( H)
        ( div-cross-mul-diff-common-divisor-mediant-fraction-ℤ
          ( x)
          ( y)
          ( gcd-ℤ n d)
          ( is-common-divisor-gcd-ℤ n d))
  in
    rec-coproduct
      ( λ K → K)
      ( λ K →
        ex-falso
          ( is-not-negative-and-nonnegative-ℤ
            ( gcd-ℤ n d)
            ( ( inv-tr
                ( is-negative-ℤ)
                ( K)
                ( _)) ,
              ( is-nonnegative-gcd-ℤ n d))))
      ( is-one-or-neg-one-is-unit-ℤ
        ( gcd-ℤ n d)
        ( is-unit-gcd-mediant))
```

## External links

- [Mediant fraction](<https://en.wikipedia.org/wiki/Mediant_(mathematics)>) at
  Wikipedia
