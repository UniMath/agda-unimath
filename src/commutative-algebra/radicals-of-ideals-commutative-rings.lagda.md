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
open import commutative-algebra.sums-commutative-rings

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.binomial-coefficients
open import elementary-number-theory.distance-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.standard-finite-types
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

{-
  is-closed-under-addition-radical-of-ideal-Commutative-Ring :
    is-closed-under-addition-subset-Commutative-Ring A
      ( subset-radical-of-ideal-Commutative-Ring)
  is-closed-under-addition-radical-of-ideal-Commutative-Ring x y f h =
    apply-universal-property-trunc-Prop f
    ( subset-radical-of-ideal-Commutative-Ring (add-Commutative-Ring A x y))
    ( λ (n , p) →
      apply-universal-property-trunc-Prop h
        ( subset-radical-of-ideal-Commutative-Ring (add-Commutative-Ring A x y))
        ( λ (m , q) →
          intro-∃
            ( add-ℕ n m)
            ( {!is-closed-under-eq-ideal-Commutative-Ring!})))
            -}
```

( binomial-theorem-Commutative-Ring A (add-ℕ n m) x y) ∙ ( (
split-sum-Commutative-Ring A n ( succ-ℕ m) ( λ i →
mul-nat-scalar-Commutative-Ring A ( binomial-coefficient-ℕ ( add-ℕ n m) (
nat-Fin (add-ℕ n (succ-ℕ m)) i)) ( mul-Commutative-Ring A (
power-Commutative-Ring A ( nat-Fin (add-ℕ n (succ-ℕ m)) i) ( x)) (
power-Commutative-Ring A ( dist-ℕ ( add-ℕ n m) ( nat-Fin (add-ℕ n (succ-ℕ m))
i)) ( y))))) ∙ ( ( ap-add-Commutative-Ring A ( ( htpy-sum-Commutative-Ring A n (
λ i → ( ap ( λ u → mul-nat-scalar-Commutative-Ring A ( binomial-coefficient-ℕ
(add-ℕ n m) u) ( mul-Commutative-Ring A ( power-Commutative-Ring A u x) (
power-Commutative-Ring A ( dist-ℕ (add-ℕ n m) u) ( y)))) ( nat-inl-coprod-Fin n
m i)) ∙ ( ( ( ap ( mul-nat-scalar-Commutative-Ring A ( binomial-coefficient-ℕ (
add-ℕ n m) ( nat-Fin n i))) ( ( ap ( mul-Commutative-Ring A (
power-Commutative-Ring A ( nat-Fin n i) ( x))) ( ( ap ( λ u →
power-Commutative-Ring A u y) ( ( symmetric-dist-ℕ ( add-ℕ n m) ( nat-Fin n i))
∙ ( ( inv ( triangle-equality-dist-ℕ ( nat-Fin n i) ( n) ( add-ℕ n m) (
upper-bound-nat-Fin' n i) ( leq-add-ℕ n m))) ∙ ( ap ( add-ℕ (dist-ℕ (nat-Fin n
i) n)) ( dist-add-ℕ n m))))) ∙ ( ( power-add-Commutative-Ring A ( dist-ℕ
(nat-Fin n i) n) ( m)) ∙ ( ( ap ( mul-Commutative-Ring A (
power-Commutative-Ring A ( dist-ℕ (nat-Fin n i) n) ( y))) ( q)) ∙ (
right-zero-law-mul-Commutative-Ring ( A) ( power-Commutative-Ring A ( dist-ℕ
(nat-Fin n i) n) ( y))))))) ∙ ( right-zero-law-mul-Commutative-Ring A (
power-Commutative-Ring A ( nat-Fin n i) ( x)))))) ∙ (
right-zero-law-mul-nat-scalar-Commutative-Ring A ( binomial-coefficient-ℕ (
add-ℕ n m) ( nat-Fin n i)))))) ∙ ( sum-zero-Commutative-Ring A n)) ( (
htpy-sum-Commutative-Ring A (succ-ℕ m) ( λ i → ( ap ( λ u →
mul-nat-scalar-Commutative-Ring A ( binomial-coefficient-ℕ (add-ℕ n m) u) (
mul-Commutative-Ring A ( power-Commutative-Ring A u x) ( power-Commutative-Ring
A ( dist-ℕ (add-ℕ n m) u) ( y)))) ( nat-inr-coprod-Fin n (succ-ℕ m) i)) ∙ ( ( ap
( mul-nat-scalar-Commutative-Ring A ( binomial-coefficient-ℕ ( add-ℕ n m) (
add-ℕ n (nat-Fin (succ-ℕ m) i)))) ( ( ap ( mul-Commutative-Ring' A (
power-Commutative-Ring A ( dist-ℕ ( add-ℕ n m) ( add-ℕ n (nat-Fin (succ-ℕ m)
i))) ( y))) ( ( power-add-Commutative-Ring A n ( nat-Fin (succ-ℕ m) i)) ∙ ( ( ap
(mul-Commutative-Ring' A _) p) ∙ ( left-zero-law-mul-Commutative-Ring A (
power-Commutative-Ring A ( nat-Fin (succ-ℕ m) i) ( x)))))) ∙ (
left-zero-law-mul-Commutative-Ring A _))) ∙ (
right-zero-law-mul-nat-scalar-Commutative-Ring A ( binomial-coefficient-ℕ (
add-ℕ n m) ( add-ℕ n (nat-Fin (succ-ℕ m) i))))))) ∙ ( sum-zero-Commutative-Ring
A (succ-ℕ m)))) ∙ ( left-unit-law-add-Commutative-Ring A ( zero-Commutative-Ring
A))))
