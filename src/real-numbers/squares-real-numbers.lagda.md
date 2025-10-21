# Squares of real numbers

```agda
module real-numbers.squares-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequalities-positive-and-negative-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.intersections-closed-intervals-rational-numbers
open import elementary-number-theory.maximum-rational-numbers
open import elementary-number-theory.multiplication-closed-intervals-rational-numbers
open import elementary-number-theory.multiplication-negative-rational-numbers
open import elementary-number-theory.multiplication-positive-and-negative-rational-numbers
open import elementary-number-theory.multiplication-positive-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.negative-rational-numbers
open import elementary-number-theory.nonnegative-rational-numbers
open import elementary-number-theory.nonpositive-rational-numbers
open import elementary-number-theory.positive-and-negative-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.squares-rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
open import real-numbers.enclosing-closed-rational-intervals-real-numbers
open import real-numbers.multiplication-nonnegative-real-numbers
open import real-numbers.multiplication-positive-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.positive-and-negative-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.strict-inequality-real-numbers
```

</details>

## Idea

The
{{#concept "square" WDID=Q111124 WD="square" Agda=square-ℝ Disambiguation="of a real number"}}
of a [real number](real-numbers.dedekind-real-numbers.md) `x` is the
[product](real-numbers.multiplication-real-numbers.md) of `x` with itself.

## Definition

```agda
square-ℝ : {l : Level} → ℝ l → ℝ l
square-ℝ x = x *ℝ x
```

## Properties

### The square of a real number is nonnegative

```agda
opaque
  unfolding mul-ℝ

  is-nonnegative-square-ℝ :
    {l : Level} (x : ℝ l) → is-nonnegative-ℝ (square-ℝ x)
  is-nonnegative-square-ℝ x =
    is-nonnegative-is-positive-upper-cut-ℝ (square-ℝ x)
      ( λ q x²<q →
        let open do-syntax-trunc-Prop (is-positive-prop-ℚ q)
        in do
          ((([a,b] , a<x<b) , ([c,d] , c<x<d)) , [a,b][c,d]<q) ← x²<q
          let
            ([a',b']@((a' , b') , _) , a'<x , x<b') =
              intersection-type-enclosing-closed-rational-interval-ℝ
                ( x)
                ( [a,b] , a<x<b)
                ( [c,d] , c<x<d)
            [a,b]∩[c,d] =
              intersect-enclosing-closed-rational-interval-ℝ
                ( x)
                ( [a,b])
                ( [c,d])
                ( a<x<b)
                ( c<x<d)
            [a',b'][a',b']<q =
              concatenate-leq-le-ℚ _ _ _
                ( pr2
                  ( preserves-leq-mul-closed-interval-ℚ
                    ( [a',b'])
                    ( [a,b])
                    ( [a',b'])
                    ( [c,d])
                    ( leq-left-intersection-closed-interval-ℚ
                      ( [a,b])
                      ( [c,d])
                      ( [a,b]∩[c,d]))
                    ( leq-right-intersection-closed-interval-ℚ
                      ( [a,b])
                      ( [c,d])
                      ( [a,b]∩[c,d]))))
                ( [a,b][c,d]<q)
          elim-disjunction
            ( is-positive-prop-ℚ q)
            ( λ a'<0 →
              let
                a'⁻ = (a' , is-negative-le-zero-ℚ a'<0)
              in
                is-positive-le-ℚ⁺
                  ( a'⁻ *ℚ⁻ a'⁻)
                  ( q)
                  ( concatenate-leq-le-ℚ
                    ( a' *ℚ a')
                    ( upper-bound-mul-closed-interval-ℚ [a',b'] [a',b'])
                    ( q)
                    ( transitive-leq-ℚ _ _ _
                      ( leq-left-max-ℚ _ _)
                      ( leq-left-max-ℚ _ _))
                    ( [a',b'][a',b']<q)))
            ( λ 0<b' →
              let
                b'⁺ = (b' , is-positive-le-zero-ℚ 0<b')
              in
                is-positive-le-ℚ⁺
                  ( b'⁺ *ℚ⁺ b'⁺)
                  ( q)
                  ( concatenate-leq-le-ℚ
                    ( b' *ℚ b')
                    ( upper-bound-mul-closed-interval-ℚ [a',b'] [a',b'])
                    ( q)
                    ( transitive-leq-ℚ _ _ _
                      ( leq-right-max-ℚ _ _)
                      ( leq-right-max-ℚ _ _))
                    ( [a',b'][a',b']<q)))
            ( located-le-ℚ zero-ℚ a' b'
              ( le-lower-upper-cut-ℝ x a' b' a'<x x<b')))

nonnegative-square-ℝ : {l : Level} → ℝ l → ℝ⁰⁺ l
nonnegative-square-ℝ x = (square-ℝ x , is-nonnegative-square-ℝ x)

square-ℝ⁰⁺ : {l : Level} → ℝ⁰⁺ l → ℝ⁰⁺ l
square-ℝ⁰⁺ x = nonnegative-square-ℝ (real-ℝ⁰⁺ x)
```

## Properties

### The canonical embedding of the rational numbers in the real numbers preserves squares

```agda
abstract
  square-real-ℚ : (q : ℚ) → square-ℝ (real-ℚ q) ＝ real-ℚ (square-ℚ q)
  square-real-ℚ q = mul-real-ℚ q q
```

### The square of the negation of `x` is the square of `x`

```agda
abstract
  square-neg-ℝ : {l : Level} (x : ℝ l) → square-ℝ (neg-ℝ x) ＝ square-ℝ x
  square-neg-ℝ x = negative-law-mul-ℝ x x
```

### Squaring distributes over multiplication

```agda
abstract
  distributive-square-mul-ℝ :
    {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2) →
    square-ℝ (x *ℝ y) ＝ square-ℝ x *ℝ square-ℝ y
  distributive-square-mul-ℝ x y = interchange-law-mul-mul-ℝ x y x y
```

### For nonnegative real numbers, squaring preserves strict inequality

```agda
abstract
  preserves-le-square-ℝ⁰⁺ :
    {l1 l2 : Level} (x : ℝ⁰⁺ l1) (y : ℝ⁰⁺ l2) → le-ℝ⁰⁺ x y →
    le-ℝ⁰⁺ (square-ℝ⁰⁺ x) (square-ℝ⁰⁺ y)
  preserves-le-square-ℝ⁰⁺ x⁰⁺@(x , _) y⁰⁺@(y , _) x<y =
    concatenate-leq-le-ℝ
      ( square-ℝ x)
      ( x *ℝ y)
      ( square-ℝ y)
      ( preserves-leq-left-mul-ℝ⁰⁺ x⁰⁺ x y (leq-le-ℝ x y x<y))
      ( preserves-le-right-mul-ℝ⁺ (y , is-positive-le-ℝ⁰⁺ x⁰⁺ y x<y) x y x<y)
```

### If a nonnegative rational `q` is in the lower cut of `x`, `q²` is in the lower cut of `x²`

```agda
abstract
  is-in-lower-cut-square-ℝ :
    {l : Level} (x : ℝ l) (q : ℚ⁰⁺) → is-in-lower-cut-ℝ x (rational-ℚ⁰⁺ q) →
    is-in-lower-cut-ℝ (square-ℝ x) (square-ℚ (rational-ℚ⁰⁺ q))
  is-in-lower-cut-square-ℝ x q⁰⁺@(q , _) q∈Lx =
    let
      qℝ = nonnegative-real-ℚ⁰⁺ q⁰⁺
      q<x = le-real-is-in-lower-cut-ℚ q x q∈Lx
    in
      is-in-lower-cut-le-real-ℚ
        ( square-ℚ q)
        ( square-ℝ x)
        ( tr
          ( λ y → le-ℝ y (square-ℝ x))
          ( square-real-ℚ q)
          ( preserves-le-square-ℝ⁰⁺
            ( qℝ)
            ( x , is-nonnegative-le-ℝ⁰⁺ qℝ x q<x)
            ( q<x)))
```

### If a rational `q` is in the upper cut of a nonnegative real number `x`, `q²` is in the upper cut of `x²`

```agda
abstract
  is-in-upper-cut-square-ℝ :
    {l : Level} (x : ℝ⁰⁺ l) (q : ℚ) → is-in-upper-cut-ℝ⁰⁺ x q →
    is-in-upper-cut-ℝ⁰⁺ (square-ℝ⁰⁺ x) (square-ℚ q)
  is-in-upper-cut-square-ℝ x⁰⁺@(x , _) q q∈Ux =
    is-in-upper-cut-le-real-ℚ
      ( square-ℚ q)
      ( square-ℝ x)
      ( tr
        ( le-ℝ (square-ℝ x))
        ( square-real-ℚ q)
        ( preserves-le-square-ℝ⁰⁺
          ( x⁰⁺)
          ( nonnegative-real-ℚ⁺
            ( q , is-positive-is-in-upper-cut-ℝ⁰⁺ x⁰⁺ q q∈Ux))
          ( le-real-is-in-upper-cut-ℚ q x q∈Ux)))
```

### If a rational `q` is in the upper cut of both `x` and `-x`, `q²` is in the upper cut of `x²`

```agda
opaque
  unfolding mul-ℝ neg-ℝ

  is-in-upper-cut-square-pos-neg-ℝ :
    {l : Level} (x : ℝ l) (q : ℚ) →
    is-in-upper-cut-ℝ x q → is-in-upper-cut-ℝ (neg-ℝ x) q →
    is-in-upper-cut-ℝ (square-ℝ x) (square-ℚ q)
  is-in-upper-cut-square-pos-neg-ℝ x q x<q -q<x =
    let
      -- this lemma follows from the absolute value being nonnegative, but
      -- for circular dependency reasons we need to prove it here
      is-pos-q =
        rec-coproduct
          ( id)
          ( λ is-nonpos-q →
            ex-falso
              ( is-disjoint-cut-ℝ
                ( x)
                ( zero-ℚ)
                ( leq-lower-cut-ℝ
                    ( x)
                    ( zero-ℚ)
                    ( neg-ℚ q)
                    ( leq-zero-is-nonnegative-ℚ
                      ( is-nonnegative-neg-is-nonpositive-ℚ is-nonpos-q))
                    ( -q<x) ,
                  leq-upper-cut-ℝ
                    ( x)
                    ( q)
                    ( zero-ℚ)
                    ( leq-zero-is-nonpositive-ℚ is-nonpos-q)
                    ( x<q))))
          ( decide-is-positive-is-nonpositive-ℚ q)
      q⁺ = (q , is-pos-q)
      [-q,q] = ((neg-ℚ q , q) , leq-negative-positive-ℚ (neg-ℚ⁺ q⁺) q⁺)
    in
      leq-upper-cut-mul-ℝ'-upper-cut-mul-ℝ x x (square-ℚ q)
        ( intro-exists
          ( ([-q,q] , -q<x , x<q) , ([-q,q] , -q<x , x<q))
          ( inv-tr
            ( λ r → leq-ℚ r (q *ℚ q))
            ( upper-bound-square-even-interval-ℚ
              ( (neg-ℚ q , q) , leq-lower-upper-cut-ℝ x (neg-ℚ q) q -q<x x<q)
              ( refl))
            ( refl-leq-ℚ (q *ℚ q))))
```
