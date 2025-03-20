# Squares in the integers

```agda
open import foundation.function-extensionality-axiom

module
  elementary-number-theory.squares-integers
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.absolute-value-integers funext
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers funext
open import elementary-number-theory.multiplication-positive-and-negative-integers funext
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonnegative-integers funext
open import elementary-number-theory.positive-and-negative-integers funext
open import elementary-number-theory.positive-integers funext
open import elementary-number-theory.squares-natural-numbers funext

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types funext
open import foundation.decidable-types funext
open import foundation.dependent-pair-types
open import foundation.identity-types funext
open import foundation.logical-equivalences funext
open import foundation.negation funext
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.transport-along-identifications
```

</details>

## Definition

```agda
square-ℤ : ℤ → ℤ
square-ℤ a = mul-ℤ a a

cube-ℤ : ℤ → ℤ
cube-ℤ a = mul-ℤ (square-ℤ a) a

is-square-ℤ : ℤ → UU lzero
is-square-ℤ a = Σ ℤ (λ x → a ＝ square-ℤ x)

square-root-ℤ : (a : ℤ) → is-square-ℤ a → ℤ
square-root-ℤ _ (root , _) = root
```

## Properties

### Squares in ℤ are nonnegative

```agda
is-nonnegative-square-ℤ : (a : ℤ) → is-nonnegative-ℤ (square-ℤ a)
is-nonnegative-square-ℤ a =
  rec-coproduct
    ( λ H → is-nonnegative-is-positive-ℤ (is-positive-mul-negative-ℤ H H))
    ( λ H → is-nonnegative-mul-ℤ H H)
    ( decide-is-negative-is-nonnegative-ℤ {a})
```

### The squares in ℤ are exactly the squares in ℕ

```agda
is-square-int-is-square-nat : {n : ℕ} → is-square-ℕ n → is-square-ℤ (int-ℕ n)
is-square-int-is-square-nat (root , pf-square) =
  ( ( int-ℕ root) ,
    ( ( ap int-ℕ pf-square) ∙
      ( inv (mul-int-ℕ root root))))

is-square-nat-is-square-int : {a : ℤ} → is-square-ℤ a → is-square-ℕ (abs-ℤ a)
is-square-nat-is-square-int (root , pf-square) =
  ( ( abs-ℤ root) ,
    ( ( ap abs-ℤ pf-square) ∙
      ( multiplicative-abs-ℤ root root)))

iff-is-square-int-is-square-nat :
  (n : ℕ) → is-square-ℕ n ↔ is-square-ℤ (int-ℕ n)
pr1 (iff-is-square-int-is-square-nat n) = is-square-int-is-square-nat
pr2 (iff-is-square-int-is-square-nat n) H =
  tr is-square-ℕ (abs-int-ℕ n) (is-square-nat-is-square-int H)

iff-is-nonneg-square-nat-is-square-int :
  (a : ℤ) → is-square-ℤ a ↔ is-nonnegative-ℤ a × is-square-ℕ (abs-ℤ a)
pr1 (iff-is-nonneg-square-nat-is-square-int a) (root , pf-square) =
  ( ( tr is-nonnegative-ℤ (inv pf-square) (is-nonnegative-square-ℤ root)) ,
    ( is-square-nat-is-square-int (root , pf-square)))
pr2
  ( iff-is-nonneg-square-nat-is-square-int a) (pf-nonneg , (root , pf-square)) =
  ( ( int-ℕ root) ,
    ( ( inv (int-abs-is-nonnegative-ℤ a pf-nonneg)) ∙
      ( pr2 (is-square-int-is-square-nat (root , pf-square)))))
```

### Squareness in ℤ is decidable

```agda
is-decidable-is-square-ℤ : (a : ℤ) → is-decidable (is-square-ℤ a)
is-decidable-is-square-ℤ (inl n) =
  inr (map-neg (pr1 (iff-is-nonneg-square-nat-is-square-int (inl n))) pr1)
is-decidable-is-square-ℤ (inr (inl n)) = inl (zero-ℤ , refl)
is-decidable-is-square-ℤ (inr (inr n)) =
  is-decidable-iff
    ( is-square-int-is-square-nat)
    ( is-square-nat-is-square-int)
    ( is-decidable-is-square-ℕ (succ-ℕ n))
```
