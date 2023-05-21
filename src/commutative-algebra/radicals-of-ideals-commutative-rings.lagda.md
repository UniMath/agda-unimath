# Radicals of ideals in commutative rings

```agda
module commutative-algebra.radicals-of-ideals-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.binomial-theorem-commutative-rings
open import commutative-algebra.commutative-rings
open import commutative-algebra.ideals-commutative-rings
open import commutative-algebra.powers-of-elements-commutative-rings
open import commutative-algebra.subsets-commutative-rings

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels
open import foundation.identity-types
```

</details>

## Idea

The **radical** of an ideal `I` in a commutative ring `A` is the ideal
consisting of all elements `f` for which there exists an `n` such that `fⁿ ∈ I`.

## Definition

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

  radical-of-ideal-Commutative-Ring : ideal-Commutative-Ring l2 A
  radical-of-ideal-Commutative-Ring =
    ideal-right-ideal-Commutative-Ring A
      subset-radical-of-ideal-Commutative-Ring
      contains-zero-radical-of-ideal-Commutative-Ring
      is-closed-under-addition-radical-of-ideal-Commutative-Ring
      is-closed-under-negatives-radical-of-ideal-Commutative-Ring
      is-closed-under-right-multiplication-radical-of-ideal-Commutative-Ring
```

## Properties

### The radical ideal of an intersection is the intersection of the radicals of the ideals

```agda
module _
  {l1 l2 l3 : Level} (A : Commutative-Ring l1)
  (I : ideal-Commutative-Ring l2 A) (J : ideal-Commutative-Ring l3 A)
  where

  preserves-intersection-radical-of-ideal-commutative-ring :
    intersection-ideal-Commutative-Ring A
    ( radical-of-ideal-Commutative-Ring A I)
    ( radical-of-ideal-Commutative-Ring A J) ＝
    radical-of-ideal-Commutative-Ring A (intersection-ideal-Commutative-Ring A I J)
  preserves-intersection-radical-of-ideal-commutative-ring =
    eq-has-same-elements-ideal-Commutative-Ring A
    (intersection-ideal-Commutative-Ring A (radical-of-ideal-Commutative-Ring A I) (radical-of-ideal-Commutative-Ring A J))
    (radical-of-ideal-Commutative-Ring A (intersection-ideal-Commutative-Ring A I J))
    {!  !}

```
