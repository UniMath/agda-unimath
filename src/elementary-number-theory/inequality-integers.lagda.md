# Inequality of integers

```agda
module elementary-number-theory.inequality-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers
open import elementary-number-theory.difference-integers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.integers
open import elementary-number-theory.natural-numbers

open import foundation.coproduct-types
open import foundation.empty-types
open import foundation.functions
open import foundation.functoriality-coproduct-types
open import foundation.identity-types
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

# Inequality on the integers

```agda
leq-ℤ : ℤ → ℤ → UU lzero
leq-ℤ x y = is-nonnegative-ℤ (diff-ℤ y x)

refl-leq-ℤ : (k : ℤ) → leq-ℤ k k
refl-leq-ℤ k = tr is-nonnegative-ℤ (inv (right-inverse-law-add-ℤ k)) star

antisymmetric-leq-ℤ : {x y : ℤ} → leq-ℤ x y → leq-ℤ y x → x ＝ y
antisymmetric-leq-ℤ {x} {y} H K =
  eq-diff-ℤ
    ( is-zero-is-nonnegative-ℤ K
      ( is-nonnegative-eq-ℤ (inv (distributive-neg-diff-ℤ x y)) H))

trans-leq-ℤ : (k l m : ℤ) → leq-ℤ k l → leq-ℤ l m → leq-ℤ k m
trans-leq-ℤ k l m p q =
  tr is-nonnegative-ℤ
    ( triangle-diff-ℤ m l k)
    ( is-nonnegative-add-ℤ
      ( add-ℤ m (neg-ℤ l))
      ( add-ℤ l (neg-ℤ k))
      ( q)
      ( p))

decide-leq-ℤ :
  {x y : ℤ} → (leq-ℤ x y) + (leq-ℤ y x)
decide-leq-ℤ {x} {y} =
  map-coprod
    ( id)
    ( is-nonnegative-eq-ℤ (distributive-neg-diff-ℤ y x))
    ( decide-is-nonnegative-ℤ {diff-ℤ y x})

succ-leq-ℤ : (k : ℤ) → leq-ℤ k (succ-ℤ k)
succ-leq-ℤ k =
  is-nonnegative-eq-ℤ
    ( inv
      ( ( left-successor-law-add-ℤ k (neg-ℤ k)) ∙
        ( ap succ-ℤ (right-inverse-law-add-ℤ k))))
    ( star)

leq-ℤ-succ-leq-ℤ : (k l : ℤ) → leq-ℤ k l → leq-ℤ k (succ-ℤ l)
leq-ℤ-succ-leq-ℤ k l p = trans-leq-ℤ k l (succ-ℤ l) p (succ-leq-ℤ l)

-- Bureaucracy

concatenate-eq-leq-eq-ℤ :
  {x' x y y' : ℤ} → x' ＝ x → leq-ℤ x y → y ＝ y' → leq-ℤ x' y'
concatenate-eq-leq-eq-ℤ refl H refl = H

concatenate-leq-eq-ℤ :
  (x : ℤ) {y y' : ℤ} → leq-ℤ x y → y ＝ y' → leq-ℤ x y'
concatenate-leq-eq-ℤ x H refl = H

concatenate-eq-leq-ℤ :
  {x x' : ℤ} (y : ℤ) → x' ＝ x → leq-ℤ x y → leq-ℤ x' y
concatenate-eq-leq-ℤ y refl H = H
```

## The strict ordering on ℤ

```agda
le-ℤ : ℤ → ℤ → UU lzero
le-ℤ x y = is-positive-ℤ (diff-ℤ x y)
```

```agda
-- We show that ℤ is an ordered ring

preserves-order-add-ℤ' :
  {x y : ℤ} (z : ℤ) → leq-ℤ x y → leq-ℤ (add-ℤ x z) (add-ℤ y z)
preserves-order-add-ℤ' {x} {y} z =
  is-nonnegative-eq-ℤ (inv (right-translation-diff-ℤ y x z))

preserves-order-add-ℤ :
  {x y : ℤ} (z : ℤ) → leq-ℤ x y → leq-ℤ (add-ℤ z x) (add-ℤ z y)
preserves-order-add-ℤ {x} {y} z =
  is-nonnegative-eq-ℤ (inv (left-translation-diff-ℤ y x z))

preserves-leq-add-ℤ :
  {a b c d : ℤ} → leq-ℤ a b → leq-ℤ c d → leq-ℤ (add-ℤ a c) (add-ℤ b d)
preserves-leq-add-ℤ {a} {b} {c} {d} H K =
  trans-leq-ℤ
    ( add-ℤ a c)
    ( add-ℤ b c)
    ( add-ℤ b d)
    ( preserves-order-add-ℤ' {a} {b} c H)
    ( preserves-order-add-ℤ b K)

reflects-order-add-ℤ' :
  {x y z : ℤ} → leq-ℤ (add-ℤ x z) (add-ℤ y z) → leq-ℤ x y
reflects-order-add-ℤ' {x} {y} {z} =
  is-nonnegative-eq-ℤ (right-translation-diff-ℤ y x z)

reflects-order-add-ℤ :
  {x y z : ℤ} → leq-ℤ (add-ℤ z x) (add-ℤ z y) → leq-ℤ x y
reflects-order-add-ℤ {x} {y} {z} =
  is-nonnegative-eq-ℤ (left-translation-diff-ℤ y x z)
```

### Inclusion of ℕ into ℤ preserves order
```agda
leq-int-ℕ : (x y : ℕ) → leq-ℕ x y → leq-ℤ (int-ℕ x) (int-ℕ y)
leq-int-ℕ zero-ℕ y H = tr (is-nonnegative-ℤ) (inv (right-unit-law-add-ℤ (int-ℕ y))) (is-nonnegative-int-ℕ y)
leq-int-ℕ (succ-ℕ x) (succ-ℕ y) H = tr (is-nonnegative-ℤ)
  (inv (diff-succ-ℤ (int-ℕ y) (int-ℕ x))
    ∙ (ap (λ H → diff-ℤ H (succ-ℤ (int-ℕ x))) (succ-int-ℕ y)
    ∙ ap (λ H → diff-ℤ (int-ℕ (succ-ℕ y)) H) (succ-int-ℕ x)))
  (leq-int-ℕ x y H)
```
