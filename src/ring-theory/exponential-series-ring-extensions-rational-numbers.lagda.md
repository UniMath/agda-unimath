# The exponential series in ring extensions of the rational numbers

```agda
module ring-theory.exponential-series-ring-extensions-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.binary-sum-decompositions-natural-numbers
open import elementary-number-theory.binomial-coefficients
open import elementary-number-theory.distance-natural-numbers
open import elementary-number-theory.factorials
open import elementary-number-theory.integers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.positive-integers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.reciprocal-factorials
open import elementary-number-theory.ring-of-rational-numbers
open import elementary-number-theory.semiring-of-natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.unital-binary-operations
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.semigroups

open import linear-algebra.finite-sequences-in-rings

open import ring-theory.binomial-theorem-rings
open import ring-theory.commuting-elements-rings
open import ring-theory.convolution-sequences-rings
open import ring-theory.convolution-sequences-semirings
open import ring-theory.integer-multiples-of-elements-rings
open import ring-theory.invertible-elements-rings
open import ring-theory.multiples-of-elements-rings
open import ring-theory.powers-of-elements-rings
open import ring-theory.ring-extensions-rational-numbers
open import ring-theory.rings
open import ring-theory.semirings
open import ring-theory.sequences-rings
open import ring-theory.sums-of-finite-families-of-elements-rings
open import ring-theory.sums-of-finite-sequences-of-elements-rings

open import univalent-combinatorics.classical-finite-types
open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.counting
open import univalent-combinatorics.dependent-pair-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The
{{#concept "exponential series" Disambiguation="in a ring extension of the rational numbers" Agda=coefficient-exponential-series-Rational-Extension-Ring WD="natural exponential function" WDID=Q47306354}}
in a [ring extension of ℚ](ring-theory.ring-extensions-rational-numbers.md) `R`
is the series with coefficients `n ↦ 1/n!`.

For any `x ∈ R`, the sequence of coefficients of the exponential series at `x`
is the sequence `exp(x) : n ↦ xⁿ/n!`.

The sequence of coefficients of the exponential series satisfy the two following
conditions:

- `exp(0) = 1`, where `1` is the unit of the
  [convolution product](ring-theory.convolution-sequences-rings.md);
- if `x , y ∈ R` [commute](ring-theory.commuting-elements-rings.md), then
  `exp(x + y) = exp(x) ⋆ exp(y)` where `⋆` denotes the convolution product.

## Definitions

### The sequence of coefficients of the exponential series

```agda
module _
  {l : Level} (R : Rational-Extension-Ring l)
  where

  coefficient-exponential-series-Rational-Extension-Ring :
    type-sequence-Ring (ring-Rational-Extension-Ring R)
  coefficient-exponential-series-Rational-Extension-Ring =
    map-initial-hom-Rational-Extension-Ring R ∘ inv-factorial-ℕ
```

### The sequence of terms of the exponential series

```agda
module _
  {l : Level} (R : Rational-Extension-Ring l)
  where

  term-ev-exponential-series-Rational-Extension-Ring :
    type-Rational-Extension-Ring R →
    type-sequence-Ring (ring-Rational-Extension-Ring R)
  term-ev-exponential-series-Rational-Extension-Ring x n =
    mul-Rational-Extension-Ring R
      ( coefficient-exponential-series-Rational-Extension-Ring R n)
      ( power-Ring (ring-Rational-Extension-Ring R) n x)
```

## Properties

### The exponential of zero is one

The sequence of terms of `exp(0)` is `(1, 0, 0, 0, ...)`, the unit of the
convolution product.

```agda
module _
  {l : Level} (R : Rational-Extension-Ring l)
  where abstract

  htpy-term-ev-zero-exponential-series-Rational-Extension-Ring :
    term-ev-exponential-series-Rational-Extension-Ring R
      ( zero-Ring (ring-Rational-Extension-Ring R)) ~
    one-Ring (convolution-sequence-Ring (ring-Rational-Extension-Ring R))
  htpy-term-ev-zero-exponential-series-Rational-Extension-Ring zero-ℕ =
    right-unit-law-mul-Ring (ring-Rational-Extension-Ring R) _ ∙
    ap
      ( map-initial-hom-Rational-Extension-Ring R)
      ( compute-zero-inv-factorial-ℕ) ∙
    preserves-one-initial-hom-Rational-Extension-Ring R
  htpy-term-ev-zero-exponential-series-Rational-Extension-Ring (succ-ℕ n) =
    ap
      ( mul-Rational-Extension-Ring R
        ( coefficient-exponential-series-Rational-Extension-Ring R (succ-ℕ n)))
      ( power-succ-Ring (ring-Rational-Extension-Ring R) n _ ∙
        right-zero-law-mul-Ring (ring-Rational-Extension-Ring R) _) ∙
    right-zero-law-mul-Ring
      ( ring-Rational-Extension-Ring R)
      ( coefficient-exponential-series-Rational-Extension-Ring R (succ-ℕ n))
```

### Relation with binomial coefficients

For any `n ∈ N` and `i ≤ n`,

```text
  1/i! * 1/(n - i)! ＝ (binomial-coefficient n i) · 1/n!
```

where `·` denotes the multiple in the ring.

```agda
module _
  {l : Level} (R : Rational-Extension-Ring l)
  where abstract

  lemma-binomial-coefficent-exponential-series-Rational-Extension-Ring :
    (n : ℕ) →
    (i : Fin (succ-ℕ n)) →
    mul-Rational-Extension-Ring R
      ( coefficient-exponential-series-Rational-Extension-Ring R
        ( nat-Fin (succ-ℕ n) i))
      ( coefficient-exponential-series-Rational-Extension-Ring R
        ( dist-ℕ (nat-Fin (succ-ℕ n) i) n)) ＝
    multiple-Ring
      ( ring-Rational-Extension-Ring R)
      ( binomial-coefficient-Fin n i)
      ( coefficient-exponential-series-Rational-Extension-Ring R n)
  lemma-binomial-coefficent-exponential-series-Rational-Extension-Ring n i =
    inv (preserves-mul-initial-hom-Rational-Extension-Ring R) ∙
    ap
      ( map-initial-hom-Rational-Extension-Ring R)
      ( inv
        ( binomial-coefficient-multiple-split-inv-factorial-formula-ℕ
          ( n)
          ( nat-Fin (succ-ℕ n) i)
          ( dist-ℕ (nat-Fin (succ-ℕ n) i) n)
          ( inv
            ( is-difference-dist-ℕ
              ( nat-Fin (succ-ℕ n) i)
              ( n)
              ( upper-bound-nat-Fin n i))))) ∙
    ap
      ( map-initial-hom-Rational-Extension-Ring R)
      ( inv
        ( integer-multiple-int-Ring
          ( ring-ℚ)
          ( binomial-coefficient-Fin n i)
          ( inv-factorial-ℕ n))) ∙
    preserves-integer-multiples-hom-Ring
      ( ring-ℚ)
      ( ring-Rational-Extension-Ring R)
      ( initial-hom-Rational-Extension-Ring R)
      ( int-ℕ (binomial-coefficient-Fin n i))
      ( inv-factorial-ℕ n) ∙
    ( integer-multiple-int-Ring
      ( ring-Rational-Extension-Ring R)
      ( binomial-coefficient-Fin n i)
      ( coefficient-exponential-series-Rational-Extension-Ring R n))
```

### Additive properties of the exponential series

The sequence of terms of the exponential series of the sum of commuting elements
in a ring is the convolution product of the exponential series of each summand;
i.e., if `x` and `y` commute, for any `n : ℕ`,

```text
  (x + y)ⁿ/n! = Σ_{i + j = n} (xⁱ/i!) (yʲ/j!)
```

so

```text
  exp(x + y) = exp(x) ⋆ exp(y)
```

```agda
module _
  {l : Level} (R : Rational-Extension-Ring l)
  where abstract

  htpy-term-ev-add-mul-convolution-exponential-series-Rational-Extension-Ring :
    (x y : type-Rational-Extension-Ring R) →
    commute-Ring (ring-Rational-Extension-Ring R) x y →
    term-ev-exponential-series-Rational-Extension-Ring R
      ( add-Rational-Extension-Ring R x y) ~
    mul-convolution-sequence-Ring
      ( ring-Rational-Extension-Ring R)
      ( term-ev-exponential-series-Rational-Extension-Ring R x)
      ( term-ev-exponential-series-Rational-Extension-Ring R y)
  htpy-term-ev-add-mul-convolution-exponential-series-Rational-Extension-Ring
    x y H n =
    ap
      ( mul-Rational-Extension-Ring R
        ( coefficient-exponential-series-Rational-Extension-Ring R n))
      ( binomial-theorem-Ring (ring-Rational-Extension-Ring R) n x y H) ∙
    left-distributive-mul-binomial-sum-fin-sequence-type-Ring
      ( ring-Rational-Extension-Ring R)
      ( n)
      ( coefficient-exponential-series-Rational-Extension-Ring R n)
      ( term-xy) ∙
    htpy-sum-fin-sequence-type-Ring
      ( ring-Rational-Extension-Ring R)
      ( succ-ℕ n)
      ( inv ∘ htpy-expand-term-binomial-exponential) ∙
    inv
      ( eq-sum-finite-sum-count-Ring
        ( ring-Rational-Extension-Ring R)
        ( Fin-Finite-Type (succ-ℕ n))
        ( count-Fin (succ-ℕ n))
        ( expand-term-binomial-exponential)) ∙
    sum-equiv-finite-Ring
      ( ring-Rational-Extension-Ring R)
      ( Fin-Finite-Type (succ-ℕ n))
      ( finite-type-binary-sum-decomposition-ℕ n)
      ( equiv-index-binomial-sum)
      ( expand-term-binomial-exponential) ∙
    htpy-sum-finite-Ring
      ( ring-Rational-Extension-Ring R)
      ( finite-type-binary-sum-decomposition-ℕ n)
      ( htpy-interchange-expand-term-binomial-exponential)
    where

    term-xy :
      fin-sequence-type-Ring
        ( ring-Rational-Extension-Ring R)
        ( succ-ℕ n)
    term-xy i =
      mul-Rational-Extension-Ring R
        ( power-Ring
          ( ring-Rational-Extension-Ring R)
          ( nat-Fin (succ-ℕ n) i)
          ( x))
        ( power-Ring
          ( ring-Rational-Extension-Ring R)
          ( dist-ℕ (nat-Fin (succ-ℕ n) i) n)
          ( y))

    term-exponential-xy :
      fin-sequence-type-Ring
        ( ring-Rational-Extension-Ring R)
        ( succ-ℕ n)
    term-exponential-xy i =
      mul-Rational-Extension-Ring R
        ( coefficient-exponential-series-Rational-Extension-Ring R n)
        ( term-xy i)

    term-binomial-exponential :
      fin-sequence-type-Ring
        ( ring-Rational-Extension-Ring R)
        ( succ-ℕ n)
    term-binomial-exponential i =
      multiple-Ring
        ( ring-Rational-Extension-Ring R)
        ( binomial-coefficient-Fin n i)
        ( term-exponential-xy i)

    expand-term-binomial-exponential :
      fin-sequence-type-Ring
        ( ring-Rational-Extension-Ring R)
        ( succ-ℕ n)
    expand-term-binomial-exponential i =
      mul-Rational-Extension-Ring R
        ( mul-Rational-Extension-Ring R
          ( coefficient-exponential-series-Rational-Extension-Ring R
            ( nat-Fin (succ-ℕ n) i))
          ( coefficient-exponential-series-Rational-Extension-Ring R
            ( dist-ℕ (nat-Fin (succ-ℕ n) i) n)))
        ( term-xy i)

    htpy-expand-term-binomial-exponential :
      expand-term-binomial-exponential ~ term-binomial-exponential
    htpy-expand-term-binomial-exponential i =
      ap
        ( λ z → mul-Rational-Extension-Ring R z (term-xy i))
        ( lemma-binomial-coefficent-exponential-series-Rational-Extension-Ring
          ( R)
          ( n)
          ( i)) ∙
      left-mul-multiple-Ring
        ( ring-Rational-Extension-Ring R)
        ( binomial-coefficient-Fin n i)
        ( coefficient-exponential-series-Rational-Extension-Ring R n)
        ( term-xy i)

    equiv-index-binomial-sum :
      equiv-Finite-Type
        ( Fin-Finite-Type (succ-ℕ n))
        ( finite-type-binary-sum-decomposition-ℕ n)
    equiv-index-binomial-sum =
      equiv-binary-sum-decomposition-leq-ℕ n ∘e
      equiv-le-succ-ℕ-leq-ℕ n ∘e
      equiv-classical-standard-Fin (succ-ℕ n)

    lemma-interchange-expand-term-binomial-exponential :
      (i j : ℕ) →
      mul-Rational-Extension-Ring R
        ( mul-Rational-Extension-Ring R
          ( coefficient-exponential-series-Rational-Extension-Ring R i)
          ( coefficient-exponential-series-Rational-Extension-Ring R j))
        ( mul-Rational-Extension-Ring R
          ( power-Ring (ring-Rational-Extension-Ring R) i x)
          ( power-Ring (ring-Rational-Extension-Ring R) j y)) ＝
      mul-Rational-Extension-Ring R
        ( term-ev-exponential-series-Rational-Extension-Ring R x i)
        ( term-ev-exponential-series-Rational-Extension-Ring R y j)
    lemma-interchange-expand-term-binomial-exponential i j =
      associative-mul-Ring (ring-Rational-Extension-Ring R) _ _ _ ∙
      ap
        ( mul-Rational-Extension-Ring R _)
        ( inv (associative-mul-Ring (ring-Rational-Extension-Ring R) _ _ _)) ∙
      ap
        ( λ z →
          mul-Rational-Extension-Ring R
            ( coefficient-exponential-series-Rational-Extension-Ring R i)
            ( mul-Rational-Extension-Ring R z
              ( power-Ring (ring-Rational-Extension-Ring R) j y)))
        ( is-central-map-initial-hom-Rational-Extension-Ring
          ( R)
          ( inv-factorial-ℕ j)
          ( power-Ring (ring-Rational-Extension-Ring R) i x)) ∙
      ap
        ( mul-Rational-Extension-Ring R _)
        ( associative-mul-Ring (ring-Rational-Extension-Ring R) _ _ _) ∙
      inv (associative-mul-Ring (ring-Rational-Extension-Ring R) _ _ _)

    htpy-interchange-expand-term-binomial-exponential :
      (ij@(i , j , K) : binary-sum-decomposition-ℕ n) →
      expand-term-binomial-exponential
        ( map-inv-equiv equiv-index-binomial-sum ij) ＝
      mul-Rational-Extension-Ring R
        ( term-ev-exponential-series-Rational-Extension-Ring R x i)
        ( term-ev-exponential-series-Rational-Extension-Ring R y j)
    htpy-interchange-expand-term-binomial-exponential ij@(i , j , K) =
      let
        idx = map-inv-equiv equiv-index-binomial-sum ij

        lemma-i : nat-Fin (succ-ℕ n) idx ＝ i
        lemma-i =
          ap
            ( pr1)
            ( is-section-map-inv-equiv equiv-index-binomial-sum ij)
      in
        binary-tr
          ( λ u v →
            expand-term-binomial-exponential idx ＝
            mul-Rational-Extension-Ring R
              ( term-ev-exponential-series-Rational-Extension-Ring R x u)
              ( term-ev-exponential-series-Rational-Extension-Ring R y v))
          ( lemma-i)
          ( ap (λ k → dist-ℕ k n) lemma-i ∙
            inv (rewrite-left-add-dist-ℕ j i n K))
          ( lemma-interchange-expand-term-binomial-exponential
            ( nat-Fin (succ-ℕ n) idx)
            ( dist-ℕ (nat-Fin (succ-ℕ n) idx) n))
```

### Exponential series are invertible elements of the convolution ring

```agda
module _
  {l : Level} (R : Rational-Extension-Ring l)
  (x : type-Rational-Extension-Ring R)
  where abstract

  htpy-left-inverse-law-mul-convolution-exponential-series-Rational-Extension-Ring :
    mul-convolution-sequence-Ring
      ( ring-Rational-Extension-Ring R)
      ( term-ev-exponential-series-Rational-Extension-Ring R
        ( neg-Ring (ring-Rational-Extension-Ring R) x))
      ( term-ev-exponential-series-Rational-Extension-Ring R x) ~
    one-Ring (convolution-sequence-Ring (ring-Rational-Extension-Ring R))
  htpy-left-inverse-law-mul-convolution-exponential-series-Rational-Extension-Ring
    n =
    inv
      ( htpy-term-ev-add-mul-convolution-exponential-series-Rational-Extension-Ring
        ( R)
        ( neg-Ring (ring-Rational-Extension-Ring R) x)
        ( x)
        ( symmetric-commute-Ring
          ( ring-Rational-Extension-Ring R)
          ( x)
          ( neg-Ring (ring-Rational-Extension-Ring R) x)
          ( commute-neg-Ring
            ( ring-Rational-Extension-Ring R)
            ( refl-commute-Ring (ring-Rational-Extension-Ring R) x)))
        ( n)) ∙
    ap
      ( λ u → term-ev-exponential-series-Rational-Extension-Ring R u n)
      ( left-inverse-law-add-Ring (ring-Rational-Extension-Ring R) x) ∙
    htpy-term-ev-zero-exponential-series-Rational-Extension-Ring R n

  left-inverse-law-mul-convolution-exponential-series-Rational-Extension-Ring :
    mul-convolution-sequence-Ring
      ( ring-Rational-Extension-Ring R)
      ( term-ev-exponential-series-Rational-Extension-Ring R
        ( neg-Ring (ring-Rational-Extension-Ring R) x))
      ( term-ev-exponential-series-Rational-Extension-Ring R x) ＝
    one-Ring (convolution-sequence-Ring (ring-Rational-Extension-Ring R))
  left-inverse-law-mul-convolution-exponential-series-Rational-Extension-Ring
    =
    eq-htpy
      htpy-left-inverse-law-mul-convolution-exponential-series-Rational-Extension-Ring

  htpy-right-inverse-law-mul-convolution-exponential-series-Rational-Extension-Ring :
    mul-convolution-sequence-Ring
      ( ring-Rational-Extension-Ring R)
      ( term-ev-exponential-series-Rational-Extension-Ring R x)
      ( term-ev-exponential-series-Rational-Extension-Ring R
        ( neg-Ring (ring-Rational-Extension-Ring R) x)) ~
    one-Ring (convolution-sequence-Ring (ring-Rational-Extension-Ring R))
  htpy-right-inverse-law-mul-convolution-exponential-series-Rational-Extension-Ring
    n =
    inv
      ( htpy-term-ev-add-mul-convolution-exponential-series-Rational-Extension-Ring
        ( R)
        ( x)
        ( neg-Ring (ring-Rational-Extension-Ring R) x)
        ( commute-neg-Ring
          ( ring-Rational-Extension-Ring R)
          ( refl-commute-Ring (ring-Rational-Extension-Ring R) x))
        ( n)) ∙
    ap
      ( λ u → term-ev-exponential-series-Rational-Extension-Ring R u n)
      ( right-inverse-law-add-Ring (ring-Rational-Extension-Ring R) x) ∙
    htpy-term-ev-zero-exponential-series-Rational-Extension-Ring R n

  right-inverse-law-mul-convolution-exponential-series-Rational-Extension-Ring :
    mul-convolution-sequence-Ring
      ( ring-Rational-Extension-Ring R)
      ( term-ev-exponential-series-Rational-Extension-Ring R x)
      ( term-ev-exponential-series-Rational-Extension-Ring R
        ( neg-Ring (ring-Rational-Extension-Ring R) x)) ＝
    one-Ring (convolution-sequence-Ring (ring-Rational-Extension-Ring R))
  right-inverse-law-mul-convolution-exponential-series-Rational-Extension-Ring
    =
    eq-htpy
      htpy-right-inverse-law-mul-convolution-exponential-series-Rational-Extension-Ring

  is-invertible-mul-convolution-exponential-series-Rational-Extension-Ring :
    is-invertible-element-Ring
      ( convolution-sequence-Ring (ring-Rational-Extension-Ring R))
      ( term-ev-exponential-series-Rational-Extension-Ring R x)
  pr1 is-invertible-mul-convolution-exponential-series-Rational-Extension-Ring
    =
    term-ev-exponential-series-Rational-Extension-Ring R
      ( neg-Ring (ring-Rational-Extension-Ring R) x)
  pr2 is-invertible-mul-convolution-exponential-series-Rational-Extension-Ring
      =
      ( right-inverse-law-mul-convolution-exponential-series-Rational-Extension-Ring ,
        left-inverse-law-mul-convolution-exponential-series-Rational-Extension-Ring)
```

## External links

- [exponential map](https://ncatlab.org/nlab/show/exponential+map) at $n$Lab
- [Exponential function](https://en.wikipedia.org/wiki/Exponential_function) at
  Wikipedia
