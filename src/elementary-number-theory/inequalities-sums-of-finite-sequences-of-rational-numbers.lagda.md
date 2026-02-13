# Inequalities for sums of finite sequences of rational numbers

```agda
module elementary-number-theory.inequalities-sums-of-finite-sequences-of-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.sums-of-finite-sequences-of-elements-commutative-rings

open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.ring-of-rational-numbers
open import elementary-number-theory.sums-of-finite-sequences-of-rational-numbers

open import foundation.coproduct-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.unit-type

open import univalent-combinatorics.standard-finite-types
```

</details>

## Theorems

```agda
abstract
  eq-sum-zero-fin-sequence-ℚ :
    (n : ℕ) →
    sum-fin-sequence-ℚ n (λ _ → zero-ℚ) ＝ zero-ℚ
  eq-sum-zero-fin-sequence-ℚ n =
    ( sum-constant-fin-sequence-ℚ n zero-ℚ) ∙
    ( right-zero-law-mul-ℚ
      ( rational-ℕ n))

  leq-zero-sum-fin-sequence-ℚ :
    (n : ℕ) (a : Fin n → ℚ) →
    ((i : Fin n) → leq-ℚ zero-ℚ (a i)) →
    leq-ℚ zero-ℚ (sum-fin-sequence-ℚ n a)
  leq-zero-sum-fin-sequence-ℚ n a nonnegative-a =
    transitive-leq-ℚ
      zero-ℚ
      ( sum-fin-sequence-ℚ n (λ _ → zero-ℚ))
      ( sum-fin-sequence-ℚ n a)
      ( preserves-leq-sum-fin-sequence-ℚ
        n
        ( λ _ → zero-ℚ)
        ( a)
        ( nonnegative-a))
      ( leq-eq-ℚ
        ( inv
          ( eq-sum-zero-fin-sequence-ℚ n)))

  leq-term-sum-fin-sequence-ℚ :
    (n : ℕ) (a : Fin n → ℚ) →
    ((i : Fin n) → leq-ℚ zero-ℚ (a i)) →
    (i : Fin n) →
    leq-ℚ (a i) (sum-fin-sequence-ℚ n a)
  leq-term-sum-fin-sequence-ℚ zero-ℕ a nonnegative-a ()
  leq-term-sum-fin-sequence-ℚ (succ-ℕ n) a nonnegative-a (inl i) =
    transitive-leq-ℚ
      ( a (inl i))
      ( sum-fin-sequence-ℚ n (a ∘ inl-Fin n) +ℚ a (inr star))
      ( sum-fin-sequence-ℚ (succ-ℕ n) a)
      ( leq-eq-ℚ
        ( inv
          ( cons-sum-fin-sequence-type-Commutative-Ring
            ( commutative-ring-ℚ)
            ( n)
            ( a)
            ( refl))))
      ( transitive-leq-ℚ
        ( a (inl i))
        ( sum-fin-sequence-ℚ n (a ∘ inl-Fin n))
        ( sum-fin-sequence-ℚ n (a ∘ inl-Fin n) +ℚ a (inr star))
        ( transitive-leq-ℚ
          ( sum-fin-sequence-ℚ n (a ∘ inl-Fin n))
          ( sum-fin-sequence-ℚ n (a ∘ inl-Fin n) +ℚ zero-ℚ)
          ( sum-fin-sequence-ℚ n (a ∘ inl-Fin n) +ℚ a (inr star))
          ( preserves-leq-right-add-ℚ
            ( sum-fin-sequence-ℚ n (a ∘ inl-Fin n))
            ( zero-ℚ)
            ( a (inr star))
            ( nonnegative-a (inr star)))
          ( leq-eq-ℚ
            ( inv
              ( right-unit-law-add-ℚ
                ( sum-fin-sequence-ℚ n (a ∘ inl-Fin n)))))
          )
        ( leq-term-sum-fin-sequence-ℚ
          n
          ( a ∘ inl-Fin n)
          ( λ j → nonnegative-a (inl j))
          ( i)))
  leq-term-sum-fin-sequence-ℚ (succ-ℕ n) a nonnegative-a (inr star) =
    transitive-leq-ℚ
      ( a (inr star))
      ( sum-fin-sequence-ℚ n (a ∘ inl-Fin n) +ℚ a (inr star))
      ( sum-fin-sequence-ℚ (succ-ℕ n) a)
      ( leq-eq-ℚ
        ( inv
          ( cons-sum-fin-sequence-type-Commutative-Ring
            ( commutative-ring-ℚ)
            ( n)
            ( a)
            ( refl))))
      ( transitive-leq-ℚ
        ( a (inr star))
        ( a (inr star) +ℚ sum-fin-sequence-ℚ n (a ∘ inl-Fin n))
        ( sum-fin-sequence-ℚ n (a ∘ inl-Fin n) +ℚ a (inr star))
        ( leq-eq-ℚ
          ( commutative-add-ℚ
            ( a (inr star))
            ( sum-fin-sequence-ℚ n (a ∘ inl-Fin n))))
        ( transitive-leq-ℚ
          ( a (inr star))
          ( a (inr star) +ℚ zero-ℚ)
          ( a (inr star) +ℚ sum-fin-sequence-ℚ n (a ∘ inl-Fin n))
          ( preserves-leq-right-add-ℚ
            ( a (inr star))
            ( zero-ℚ)
            ( sum-fin-sequence-ℚ n (a ∘ inl-Fin n))
            ( leq-zero-sum-fin-sequence-ℚ
              n
              ( a ∘ inl-Fin n)
              ( λ j → nonnegative-a (inl j))))
          ( leq-eq-ℚ
            ( inv
              ( right-unit-law-add-ℚ
                ( a (inr star)))))))
```
