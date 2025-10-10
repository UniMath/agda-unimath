# Squares of real numbers

```agda
module real-numbers.squares-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.intersections-closed-intervals-rational-numbers
open import elementary-number-theory.maximum-rational-numbers
open import elementary-number-theory.multiplication-closed-intervals-rational-numbers
open import elementary-number-theory.multiplication-negative-rational-numbers
open import elementary-number-theory.multiplication-positive-and-negative-rational-numbers
open import elementary-number-theory.multiplication-positive-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.negative-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.propositional-truncations
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
open import real-numbers.enclosing-closed-rational-intervals-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.nonnegative-real-numbers
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
                a'⁻ = (a' , is-negative-le-zero-ℚ a' a'<0)
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
                b'⁺ = (b' , is-positive-le-zero-ℚ b' 0<b')
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
```
