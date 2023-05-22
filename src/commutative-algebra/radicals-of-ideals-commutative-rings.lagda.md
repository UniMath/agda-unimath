# Radicals of ideals in commutative rings

```agda
module commutative-algebra.radicals-of-ideals-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.binomial-theorem-commutative-rings
open import commutative-algebra.commutative-rings
open import commutative-algebra.ideals-commutative-rings
open import commutative-algebra.poset-of-ideals-commutative-rings
open import commutative-algebra.powers-of-elements-commutative-rings
open import commutative-algebra.radical-ideals-commutative-rings
open import commutative-algebra.subsets-commutative-rings

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

The **radical** of an ideal `I` in a commutative ring `A` is the ideal
consisting of all elements `f` for which there exists an `n` such that `fⁿ ∈ I`.

## Definitions

### The condition of being the radical of an ideal

```agda
module _
  {l1 l2 l3 : Level} (A : Commutative-Ring l1)
  (I : ideal-Commutative-Ring l2 A)
  (J : radical-ideal-Commutative-Ring l3 A)
  (H :
    leq-ideal-Commutative-Ring A I (ideal-radical-ideal-Commutative-Ring A J))
  where

  is-radical-of-ideal-Commutative-Ring : UUω
  is-radical-of-ideal-Commutative-Ring =
    {l4 : Level} (K : radical-ideal-Commutative-Ring l4 A) →
    leq-ideal-Commutative-Ring A I (ideal-radical-ideal-Commutative-Ring A K) →
    leq-ideal-Commutative-Ring A
      ( ideal-radical-ideal-Commutative-Ring A J)
      ( ideal-radical-ideal-Commutative-Ring A K)
```

### The radical of an ideal

```agda
module _
  {l1 l2 : Level} (A : Commutative-Ring l1) (I : ideal-Commutative-Ring l2 A)
  where

  subset-radical-of-ideal-Commutative-Ring : type-Commutative-Ring A → Prop l2
  subset-radical-of-ideal-Commutative-Ring f =
    ∃-Prop ℕ
      ( λ n → is-in-ideal-Commutative-Ring A I (power-Commutative-Ring A n f))

  is-in-radical-of-ideal-Commutative-Ring : type-Commutative-Ring A → UU l2
  is-in-radical-of-ideal-Commutative-Ring =
    is-in-subtype subset-radical-of-ideal-Commutative-Ring

  contains-ideal-radical-of-ideal-Commutative-Ring :
    (f : type-Commutative-Ring A) →
    is-in-ideal-Commutative-Ring A I f →
    is-in-radical-of-ideal-Commutative-Ring f
  contains-ideal-radical-of-ideal-Commutative-Ring f H = intro-∃ 1 H

  contains-zero-radical-of-ideal-Commutative-Ring :
    is-in-radical-of-ideal-Commutative-Ring (zero-Commutative-Ring A)
  contains-zero-radical-of-ideal-Commutative-Ring =
    contains-ideal-radical-of-ideal-Commutative-Ring
      ( zero-Commutative-Ring A)
      ( contains-zero-ideal-Commutative-Ring A I)

  is-closed-under-addition-radical-of-ideal-Commutative-Ring :
    is-closed-under-addition-subset-Commutative-Ring A
      ( subset-radical-of-ideal-Commutative-Ring)
  is-closed-under-addition-radical-of-ideal-Commutative-Ring x y H K =
    apply-universal-property-trunc-Prop H
      ( subset-radical-of-ideal-Commutative-Ring (add-Commutative-Ring A x y))
      ( λ (n , p) →
        apply-universal-property-trunc-Prop K
          ( subset-radical-of-ideal-Commutative-Ring
            ( add-Commutative-Ring A x y))
          ( λ (m , q) →
            intro-∃
              ( n +ℕ m)
              ( is-closed-under-eq-ideal-Commutative-Ring' A I
                ( is-closed-under-addition-ideal-Commutative-Ring A I _ _
                  ( is-closed-under-right-multiplication-ideal-Commutative-Ring
                    ( A)
                    ( I)
                    ( _)
                    ( _)
                    ( q))
                  ( is-closed-under-right-multiplication-ideal-Commutative-Ring
                    ( A)
                    ( I)
                    ( _)
                    ( _)
                    ( p)))
                ( is-linear-combination-power-add-Commutative-Ring A n m x y))))

  is-closed-under-negatives-radical-of-ideal-Commutative-Ring :
    is-closed-under-negatives-subset-Commutative-Ring A
      ( subset-radical-of-ideal-Commutative-Ring)
  is-closed-under-negatives-radical-of-ideal-Commutative-Ring x H =
    apply-universal-property-trunc-Prop H
      ( subset-radical-of-ideal-Commutative-Ring (neg-Commutative-Ring A x))
      ( λ (n , p) →
        intro-∃ n
          ( is-closed-under-eq-ideal-Commutative-Ring' A I
            ( is-closed-under-left-multiplication-ideal-Commutative-Ring A I _
              ( power-Commutative-Ring A n x)
              ( p))
            ( power-neg-Commutative-Ring A n x)))

  is-closed-under-right-multiplication-radical-of-ideal-Commutative-Ring :
    is-closed-under-right-multiplication-subset-Commutative-Ring A
      ( subset-radical-of-ideal-Commutative-Ring)
  is-closed-under-right-multiplication-radical-of-ideal-Commutative-Ring x y H =
    apply-universal-property-trunc-Prop H
      ( subset-radical-of-ideal-Commutative-Ring (mul-Commutative-Ring A x y))
      ( λ (n , p) →
        intro-∃ n
          ( is-closed-under-eq-ideal-Commutative-Ring' A I
            ( is-closed-under-right-multiplication-ideal-Commutative-Ring A I
              ( power-Commutative-Ring A n x)
              ( power-Commutative-Ring A n y)
              ( p))
            ( distributive-power-mul-Commutative-Ring A n x y)))

  is-closed-under-left-multiplication-radical-of-ideal-Commutative-Ring :
    is-closed-under-left-multiplication-subset-Commutative-Ring A
      ( subset-radical-of-ideal-Commutative-Ring)
  is-closed-under-left-multiplication-radical-of-ideal-Commutative-Ring x y H =
    apply-universal-property-trunc-Prop H
      ( subset-radical-of-ideal-Commutative-Ring (mul-Commutative-Ring A x y))
      ( λ (n , p) →
        intro-∃ n
          ( is-closed-under-eq-ideal-Commutative-Ring' A I
            ( is-closed-under-left-multiplication-ideal-Commutative-Ring A I
              ( power-Commutative-Ring A n x)
              ( power-Commutative-Ring A n y)
              ( p))
            ( distributive-power-mul-Commutative-Ring A n x y)))

  ideal-radical-of-ideal-Commutative-Ring : ideal-Commutative-Ring l2 A
  ideal-radical-of-ideal-Commutative-Ring =
    ideal-right-ideal-Commutative-Ring A
      subset-radical-of-ideal-Commutative-Ring
      contains-zero-radical-of-ideal-Commutative-Ring
      is-closed-under-addition-radical-of-ideal-Commutative-Ring
      is-closed-under-negatives-radical-of-ideal-Commutative-Ring
      is-closed-under-right-multiplication-radical-of-ideal-Commutative-Ring

  is-radical-radical-of-ideal-Commutative-Ring :
    is-radical-ideal-Commutative-Ring A ideal-radical-of-ideal-Commutative-Ring
  is-radical-radical-of-ideal-Commutative-Ring x n H =
    apply-universal-property-trunc-Prop H
      ( subset-radical-of-ideal-Commutative-Ring x)
      ( λ (m , K) →
        intro-∃
          ( mul-ℕ n m)
          ( is-closed-under-eq-ideal-Commutative-Ring' A I K
            ( power-mul-Commutative-Ring A n m)))

  radical-of-ideal-Commutative-Ring :
    radical-ideal-Commutative-Ring l2 A
  pr1 radical-of-ideal-Commutative-Ring =
    ideal-radical-of-ideal-Commutative-Ring
  pr2 radical-of-ideal-Commutative-Ring =
    is-radical-radical-of-ideal-Commutative-Ring

  is-radical-of-ideal-radical-of-ideal-Commutative-Ring :
    is-radical-of-ideal-Commutative-Ring A I
      ( radical-of-ideal-Commutative-Ring)
      ( contains-ideal-radical-of-ideal-Commutative-Ring)
  is-radical-of-ideal-radical-of-ideal-Commutative-Ring J H x K =
    apply-universal-property-trunc-Prop K
      ( subset-radical-ideal-Commutative-Ring A J x)
      ( λ (n , L) →
        is-radical-radical-ideal-Commutative-Ring A J x n
          ( H (power-Commutative-Ring A n x) L))
```

## Properties

### The radical ideal of an intersection is the intersection of the radicals of the ideals

```agda
module _
  {l1 l2 l3 : Level} (A : Commutative-Ring l1)
  (I : ideal-Commutative-Ring l2 A) (J : ideal-Commutative-Ring l3 A)
  where

  forward-inclusion-intersection-radical-of-ideal-Commutative-Ring :
    leq-ideal-Commutative-Ring A
      ( intersection-ideal-Commutative-Ring A
        ( ideal-radical-of-ideal-Commutative-Ring A I)
        ( ideal-radical-of-ideal-Commutative-Ring A J))
      ( ideal-radical-of-ideal-Commutative-Ring A
        ( intersection-ideal-Commutative-Ring A I J))
  forward-inclusion-intersection-radical-of-ideal-Commutative-Ring x (H , K) =
    apply-universal-property-trunc-Prop H
      ( subset-radical-of-ideal-Commutative-Ring A
        ( intersection-ideal-Commutative-Ring A I J)
        ( x))
      ( λ (n , H') →
        apply-universal-property-trunc-Prop K
          ( subset-radical-of-ideal-Commutative-Ring A
            ( intersection-ideal-Commutative-Ring A I J)
            ( x))
          ( λ (m , K') →
            intro-∃
              ( add-ℕ n m)
              ( ( is-closed-under-eq-ideal-Commutative-Ring A I
                  ( is-closed-under-right-multiplication-ideal-Commutative-Ring
                    ( A)
                    ( I)
                    ( power-Commutative-Ring A n x)
                    ( power-Commutative-Ring A m x)
                    ( H'))
                  ( inv ( power-add-Commutative-Ring A n m))) ,
                ( is-closed-under-eq-ideal-Commutative-Ring A J
                  ( is-closed-under-left-multiplication-ideal-Commutative-Ring
                    ( A)
                    ( J)
                    ( power-Commutative-Ring A n x)
                    ( power-Commutative-Ring A m x)
                    ( K'))
                  ( inv ( power-add-Commutative-Ring A n m))))))

  backward-inclusion-intersection-radical-of-ideal-Commutative-Ring :
    leq-ideal-Commutative-Ring A
      ( ideal-radical-of-ideal-Commutative-Ring A
        ( intersection-ideal-Commutative-Ring A I J))
      ( intersection-ideal-Commutative-Ring A
        ( ideal-radical-of-ideal-Commutative-Ring A I)
        ( ideal-radical-of-ideal-Commutative-Ring A J))
  backward-inclusion-intersection-radical-of-ideal-Commutative-Ring x H =
    apply-universal-property-trunc-Prop H
      ( subset-intersection-ideal-Commutative-Ring A
        ( ideal-radical-of-ideal-Commutative-Ring A I)
        ( ideal-radical-of-ideal-Commutative-Ring A J)
        ( x))
      ( λ (n , H' , K') → (intro-∃ n H' , intro-∃ n K'))

  preserves-intersection-radical-of-ideal-Commutative-Ring :
    ( intersection-ideal-Commutative-Ring A
      ( ideal-radical-of-ideal-Commutative-Ring A I)
      ( ideal-radical-of-ideal-Commutative-Ring A J)) ＝
    ( ideal-radical-of-ideal-Commutative-Ring A
      ( intersection-ideal-Commutative-Ring A I J))
  preserves-intersection-radical-of-ideal-Commutative-Ring =
    eq-has-same-elements-ideal-Commutative-Ring A
      ( intersection-ideal-Commutative-Ring A
        ( ideal-radical-of-ideal-Commutative-Ring A I)
        ( ideal-radical-of-ideal-Commutative-Ring A J))
      ( ideal-radical-of-ideal-Commutative-Ring A
        ( intersection-ideal-Commutative-Ring A I J))
      ( λ x →
        forward-inclusion-intersection-radical-of-ideal-Commutative-Ring x ,
        backward-inclusion-intersection-radical-of-ideal-Commutative-Ring x)
```
