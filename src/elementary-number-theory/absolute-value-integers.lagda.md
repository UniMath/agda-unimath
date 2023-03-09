# The absolute value function on the integers

```agda
module elementary-number-theory.absolute-value-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equational-reasoning
open import foundation.functions
open import foundation.identity-types
open import foundation.unit-type
```

</details>

# The absolute value of integers

```
abs-ℤ : ℤ → ℕ
abs-ℤ (inl x) = succ-ℕ x
abs-ℤ (inr (inl star)) = zero-ℕ
abs-ℤ (inr (inr x)) = succ-ℕ x

int-abs-ℤ : ℤ → ℤ
int-abs-ℤ = int-ℕ ∘ abs-ℤ

abs-int-ℕ : (x : ℕ) → abs-ℤ (int-ℕ x) ＝ x
abs-int-ℕ zero-ℕ = refl
abs-int-ℕ (succ-ℕ x) = refl

abs-neg-ℤ : (x : ℤ) → abs-ℤ (neg-ℤ x) ＝ abs-ℤ x
abs-neg-ℤ (inl x) = refl
abs-neg-ℤ (inr (inl star)) = refl
abs-neg-ℤ (inr (inr x)) = refl

int-abs-is-nonnegative-ℤ : (x : ℤ) → is-nonnegative-ℤ x → int-abs-ℤ x ＝ x
int-abs-is-nonnegative-ℤ (inr (inl star)) h = refl
int-abs-is-nonnegative-ℤ (inr (inr x)) h = refl

eq-abs-ℤ : (x : ℤ) → is-zero-ℕ (abs-ℤ x) → is-zero-ℤ x
eq-abs-ℤ (inr (inl star)) p = refl

abs-eq-ℤ : (x : ℤ) → is-zero-ℤ x → is-zero-ℕ (abs-ℤ x)
abs-eq-ℤ .zero-ℤ refl = refl

predecessor-law-abs-ℤ :
  (x : ℤ) → (abs-ℤ (pred-ℤ x)) ≤-ℕ (succ-ℕ (abs-ℤ x))
predecessor-law-abs-ℤ (inl x) =
  refl-leq-ℕ (succ-ℕ x)
predecessor-law-abs-ℤ (inr (inl star)) =
  refl-leq-ℕ zero-ℕ
predecessor-law-abs-ℤ (inr (inr zero-ℕ)) =
  star
predecessor-law-abs-ℤ (inr (inr (succ-ℕ x))) =
  preserves-leq-succ-ℕ x (succ-ℕ x) (succ-leq-ℕ x)

successor-law-abs-ℤ :
  (x : ℤ) → (abs-ℤ (succ-ℤ x)) ≤-ℕ (succ-ℕ (abs-ℤ x))
successor-law-abs-ℤ (inl zero-ℕ) =
  star
successor-law-abs-ℤ (inl (succ-ℕ x)) =
  preserves-leq-succ-ℕ x (succ-ℕ x) (succ-leq-ℕ x)
successor-law-abs-ℤ (inr (inl star)) =
  refl-leq-ℕ zero-ℕ
successor-law-abs-ℤ (inr (inr x)) =
  refl-leq-ℕ (succ-ℕ x)

subadditive-abs-ℤ :
  (x y : ℤ) → (abs-ℤ (add-ℤ x y)) ≤-ℕ (add-ℕ (abs-ℤ x) (abs-ℤ y))
subadditive-abs-ℤ x (inl zero-ℕ) =
  concatenate-eq-leq-eq-ℕ
    ( ap abs-ℤ (add-neg-one-right-ℤ x))
    ( predecessor-law-abs-ℤ x)
    ( refl)
subadditive-abs-ℤ x (inl (succ-ℕ y)) =
  concatenate-eq-leq-eq-ℕ
    ( ap abs-ℤ (right-predecessor-law-add-ℤ x (inl y)))
    ( transitive-leq-ℕ
      ( abs-ℤ (pred-ℤ (add-ℤ x (inl y))))
      ( succ-ℕ (abs-ℤ (add-ℤ x (inl y))))
      ( add-ℕ (abs-ℤ x) (succ-ℕ (succ-ℕ y)))
      ( subadditive-abs-ℤ x (inl y))
      ( predecessor-law-abs-ℤ (add-ℤ x (inl y))))
    ( refl)
subadditive-abs-ℤ x (inr (inl star)) =
  concatenate-eq-leq-eq-ℕ
    ( ap abs-ℤ (right-unit-law-add-ℤ x))
    ( refl-leq-ℕ (abs-ℤ x))
    ( refl)
subadditive-abs-ℤ x (inr (inr zero-ℕ)) =
  concatenate-eq-leq-eq-ℕ
    ( ap abs-ℤ (add-one-right-ℤ x))
    ( successor-law-abs-ℤ x)
    ( refl)
subadditive-abs-ℤ x (inr (inr (succ-ℕ y))) =
  concatenate-eq-leq-eq-ℕ
    ( ap abs-ℤ (right-successor-law-add-ℤ x (inr (inr y))))
    ( transitive-leq-ℕ
      ( abs-ℤ (succ-ℤ (add-ℤ x (inr (inr y)))))
      ( succ-ℕ (abs-ℤ (add-ℤ x (inr (inr y)))))
      ( succ-ℕ (add-ℕ (abs-ℤ x) (succ-ℕ y)))
      ( subadditive-abs-ℤ x (inr (inr y)))
      ( successor-law-abs-ℤ (add-ℤ x (inr (inr y)))))
    ( refl)

negative-law-abs-ℤ :
  (x : ℤ) → abs-ℤ (neg-ℤ x) ＝ abs-ℤ x
negative-law-abs-ℤ (inl x) = refl
negative-law-abs-ℤ (inr (inl star)) = refl
negative-law-abs-ℤ (inr (inr x)) = refl

is-positive-abs-ℤ :
  (x : ℤ) → is-positive-ℤ x → is-positive-ℤ (int-abs-ℤ x)
is-positive-abs-ℤ (inr (inr x)) H = star

is-nonzero-abs-ℤ :
  (x : ℤ) → is-positive-ℤ x → is-nonzero-ℕ (abs-ℤ x)
is-nonzero-abs-ℤ (inr (inr x)) H = is-nonzero-succ-ℕ x

```

### Absolute value is multiplicative
```agda
neg-left-abs-ℤ-mul-ℤ : (x y : ℤ) → abs-ℤ (mul-ℤ x y) ＝ abs-ℤ (mul-ℤ (neg-ℤ x) y)
neg-left-abs-ℤ-mul-ℤ x y = equational-reasoning
  abs-ℤ (mul-ℤ x y)
  ＝ abs-ℤ (neg-ℤ (mul-ℤ x y)) by (inv (negative-law-abs-ℤ (mul-ℤ x y)))
  ＝ abs-ℤ (mul-ℤ (neg-ℤ x) y) by (ap abs-ℤ (inv (left-negative-law-mul-ℤ x y)))

neg-right-abs-ℤ-mul-ℤ : (x y : ℤ) → abs-ℤ (mul-ℤ x y) ＝ abs-ℤ (mul-ℤ x (neg-ℤ y))
neg-right-abs-ℤ-mul-ℤ x y = equational-reasoning
  abs-ℤ (mul-ℤ x y)
  ＝ abs-ℤ (neg-ℤ (mul-ℤ x y)) by (inv (negative-law-abs-ℤ (mul-ℤ x y)))
  ＝ abs-ℤ (mul-ℤ x (neg-ℤ y)) by (ap abs-ℤ (inv (right-negative-law-mul-ℤ x y)))

neg-both-abs-ℤ-mul-ℤ : (x y : ℤ) → abs-ℤ (mul-ℤ x y) ＝ abs-ℤ (mul-ℤ (neg-ℤ x) (neg-ℤ y))
neg-both-abs-ℤ-mul-ℤ x y = (neg-right-abs-ℤ-mul-ℤ x y) ∙ (neg-left-abs-ℤ-mul-ℤ x (neg-ℤ y))

int-ℕ-abs-ℤ-mult-positive-ints : (x y : ℕ) →
  int-ℕ (abs-ℤ (mul-ℤ (inr (inr x)) (inr (inr y))))
  ＝ int-ℕ (mul-ℕ (abs-ℤ (inr (inr x))) (abs-ℤ (inr (inr y))))
int-ℕ-abs-ℤ-mult-positive-ints x y = equational-reasoning
  int-ℕ (abs-ℤ (mul-ℤ (inr (inr x)) (inr (inr y))))
    ＝ mul-ℤ (inr (inr x)) (inr (inr y))
      by (int-abs-is-nonnegative-ℤ (mul-ℤ (inr (inr x)) (inr (inr y)))
        (is-nonnegative-is-positive-ℤ
          (is-positive-mul-ℤ {inr (inr x)} {inr (inr y)} star star)))
    ＝ mul-ℤ (int-ℕ (abs-ℤ (inr (inr x)))) (inr (inr y))
      by (ap (λ H → mul-ℤ H (inr (inr y)))
        (int-abs-is-nonnegative-ℤ (inr (inr x))
          (is-nonnegative-is-positive-ℤ {inr (inr x)} star)))
    ＝ mul-ℤ (int-ℕ (abs-ℤ (inr (inr x)))) (int-ℕ (abs-ℤ (inr (inr y))))
      by (ap (λ H → mul-ℤ (int-ℕ (abs-ℤ (inr (inr x)))) H)
        (int-abs-is-nonnegative-ℤ (inr (inr y))
          (is-nonnegative-is-positive-ℤ {inr (inr y)} star)))
    ＝ int-ℕ (mul-ℕ (abs-ℤ (inr (inr x))) (abs-ℤ (inr (inr y))))
      by (mul-int-ℕ (abs-ℤ (inr (inr x))) (abs-ℤ (inr (inr y))))

multiplicative-abs-ℤ : (x y : ℤ) → abs-ℤ (mul-ℤ x y) ＝ mul-ℕ (abs-ℤ x) (abs-ℤ y)
multiplicative-abs-ℤ (inl x) (inl y) = is-injective-int-ℕ
  (equational-reasoning
    int-ℕ (abs-ℤ (mul-ℤ (inl x) (inl y)))
    ＝ int-ℕ (abs-ℤ (mul-ℤ (inr (inr x)) (inr (inr y))))
      by (ap int-ℕ (neg-both-abs-ℤ-mul-ℤ (inl x) (inl y)))
    ＝ int-ℕ (mul-ℕ (abs-ℤ (inr (inr x))) (abs-ℤ (inr (inr y))))
      by (int-ℕ-abs-ℤ-mult-positive-ints x y))
multiplicative-abs-ℤ (inl x) (inr (inl star)) = equational-reasoning
  abs-ℤ (mul-ℤ (inl x) zero-ℤ)
  ＝ zero-ℕ by (ap (abs-ℤ) (right-zero-law-mul-ℤ (inl x)))
  ＝ mul-ℕ (abs-ℤ (inl x)) zero-ℕ by (inv (right-zero-law-mul-ℕ (abs-ℤ (inl x))))
multiplicative-abs-ℤ (inl x) (inr (inr y)) = is-injective-int-ℕ
  (equational-reasoning
    int-ℕ (abs-ℤ (mul-ℤ (inl x) (inr (inr y))))
    ＝ int-ℕ (abs-ℤ (mul-ℤ (inr (inr x)) (inr (inr y))))
      by (ap int-ℕ (neg-left-abs-ℤ-mul-ℤ (inl x) (inr (inr y))))
    ＝ int-ℕ (mul-ℕ (abs-ℤ (inr (inr x))) (abs-ℤ (inr (inr y))))
      by (int-ℕ-abs-ℤ-mult-positive-ints x y))
multiplicative-abs-ℤ (inr (inl star)) y = refl
multiplicative-abs-ℤ (inr (inr x)) (inl y) = is-injective-int-ℕ
  (equational-reasoning
    int-ℕ (abs-ℤ (mul-ℤ (inr (inr x)) (inl y)))
    ＝ int-ℕ (abs-ℤ (mul-ℤ (inr (inr x)) (inr (inr y))))
      by (ap int-ℕ (neg-right-abs-ℤ-mul-ℤ (inr (inr x)) (inl y)))
    ＝ int-ℕ (mul-ℕ (abs-ℤ (inr (inr x))) (abs-ℤ (inr (inr y))))
      by (int-ℕ-abs-ℤ-mult-positive-ints x y))
multiplicative-abs-ℤ (inr (inr x)) (inr (inl star)) = equational-reasoning
  abs-ℤ (mul-ℤ (inr (inr x)) zero-ℤ)
  ＝ zero-ℕ by (ap (abs-ℤ) (right-zero-law-mul-ℤ (inr (inr x))))
  ＝ mul-ℕ (abs-ℤ (inr (inr x))) zero-ℕ by (inv (right-zero-law-mul-ℕ (abs-ℤ (inr (inr x)))))
multiplicative-abs-ℤ (inr (inr x)) (inr (inr y)) = is-injective-int-ℕ
  (int-ℕ-abs-ℤ-mult-positive-ints x y)

```
