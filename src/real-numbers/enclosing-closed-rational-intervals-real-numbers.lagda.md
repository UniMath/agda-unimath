# Enclosing closed rational intervals of Dedekind real numbers

```agda
module real-numbers.enclosing-closed-rational-intervals-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.closed-intervals-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.interior-closed-intervals-rational-numbers
open import elementary-number-theory.intersections-closed-intervals-rational-numbers
open import elementary-number-theory.maximum-rational-numbers
open import elementary-number-theory.minimum-rational-numbers
open import elementary-number-theory.rational-numbers

open import foundation.conjunction
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.inhabited-types
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
```

</details>

## Idea

An enclosing
[closed rational interval](elementary-number-theory.closed-intervals-rational-numbers.md)
of a [Dedekind real number](real-numbers.dedekind-real-numbers.md) `x` is a
closed interval of rational numbers whose lower bound is in the lower cut of `x`
and whose upper count is in the upper cut of `x`.

## Definition

```agda
module _
  {l : Level} (x : ℝ l)
  where

  enclosing-closed-rational-interval-ℝ : subtype l closed-interval-ℚ
  enclosing-closed-rational-interval-ℝ ((p , q) , _) =
    lower-cut-ℝ x p ∧ upper-cut-ℝ x q

  is-enclosing-closed-rational-interval-ℝ : closed-interval-ℚ → UU l
  is-enclosing-closed-rational-interval-ℝ [p,q] =
    type-Prop (enclosing-closed-rational-interval-ℝ [p,q])

  type-enclosing-closed-rational-interval-ℝ : UU l
  type-enclosing-closed-rational-interval-ℝ =
    type-subtype enclosing-closed-rational-interval-ℝ
```

## Properties

### There exists a rational enclosing interval around each real number

```agda
module _
  {l : Level} (x : ℝ l)
  where

  abstract
    is-inhabited-type-enclosing-closed-rational-interval-ℝ :
      is-inhabited (type-enclosing-closed-rational-interval-ℝ x)
    is-inhabited-type-enclosing-closed-rational-interval-ℝ =
      let
        open
          do-syntax-trunc-Prop
            ( is-inhabited-Prop (type-enclosing-closed-rational-interval-ℝ x))
      in do
        (p , p<x) ← is-inhabited-lower-cut-ℝ x
        (q , x<q) ← is-inhabited-upper-cut-ℝ x
        intro-exists
          ( (p , q) , leq-lower-upper-cut-ℝ x p q p<x x<q)
          ( p<x , x<q)
```

### For any rational enclosing interval around a real number, there exists an interior enclosing interval

```agda
module _
  {l : Level} (x : ℝ l)
  where

  abstract
    exists-interior-enclosing-closed-rational-interval-ℝ :
      ([a,b] : closed-interval-ℚ) →
      is-enclosing-closed-rational-interval-ℝ x [a,b] →
      exists
        ( closed-interval-ℚ)
        ( λ [c,d] →
          enclosing-closed-rational-interval-ℝ x [c,d] ∧
          is-interior-prop-closed-interval-ℚ [a,b] [c,d])
    exists-interior-enclosing-closed-rational-interval-ℝ
      [a,b]@((a , b) , _) (a<x , x<b) =
      let
        open
          do-syntax-trunc-Prop
            ( ∃
              ( closed-interval-ℚ)
              ( λ [c,d] →
                enclosing-closed-rational-interval-ℝ x [c,d] ∧
                is-interior-prop-closed-interval-ℚ [a,b] [c,d]))
      in do
        (a' , a<a' , a'<x) ←
          forward-implication (is-rounded-lower-cut-ℝ x a) a<x
        (b' , b'<b , x<b') ←
          forward-implication (is-rounded-upper-cut-ℝ x b) x<b
        intro-exists
          ( (a' , b') , leq-lower-upper-cut-ℝ x a' b' a'<x x<b')
          ( ( a'<x , x<b') , (a<a' , b'<b))
```

### Any two rational enclosing intervals around a real number intersect

```agda
module _
  {l : Level} (x : ℝ l)
  where

  abstract
    intersect-enclosing-closed-rational-interval-ℝ :
      ([a,b] [c,d] : closed-interval-ℚ) →
      is-enclosing-closed-rational-interval-ℝ x [a,b] →
      is-enclosing-closed-rational-interval-ℝ x [c,d] →
      intersect-closed-interval-ℚ [a,b] [c,d]
    intersect-enclosing-closed-rational-interval-ℝ
      [a,b]@((a , b) , _) [c,d]@((c , d) , _) (a<x , x<b) (c<x , x<d) =
      ( leq-lower-upper-cut-ℝ x a d a<x x<d ,
        leq-lower-upper-cut-ℝ x c b c<x x<b)

    is-enclosing-intersection-enclosing-closed-rational-interval-ℝ :
      ([a,b] [c,d] : closed-interval-ℚ) →
      (H : is-enclosing-closed-rational-interval-ℝ x [a,b]) →
      (K : is-enclosing-closed-rational-interval-ℝ x [c,d]) →
      is-enclosing-closed-rational-interval-ℝ
        ( x)
        ( intersection-closed-interval-ℚ [a,b] [c,d]
          ( intersect-enclosing-closed-rational-interval-ℝ [a,b] [c,d] H K))
    is-enclosing-intersection-enclosing-closed-rational-interval-ℝ
      ( (a , b) , _) ((c , d) , _) (a<x , x<b) (c<x , x<d) =
      ( is-in-lower-cut-max-ℚ x a c a<x c<x ,
        is-in-upper-cut-min-ℚ x b d x<b x<d)

  intersection-type-enclosing-closed-rational-interval-ℝ :
    type-enclosing-closed-rational-interval-ℝ x →
    type-enclosing-closed-rational-interval-ℝ x →
    type-enclosing-closed-rational-interval-ℝ x
  intersection-type-enclosing-closed-rational-interval-ℝ
    ( [a,b] , H) ([c,d] , K) =
    ( intersection-closed-interval-ℚ [a,b] [c,d]
        ( intersect-enclosing-closed-rational-interval-ℝ [a,b] [c,d] H K) ,
      is-enclosing-intersection-enclosing-closed-rational-interval-ℝ
        ( [a,b])
        ( [c,d])
        ( H)
        ( K))
```
