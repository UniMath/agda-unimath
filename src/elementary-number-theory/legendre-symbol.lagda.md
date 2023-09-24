# Legendre Symbol

```agda
module elementary-number-theory.legendre-symbol where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.absolute-value-integers
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.decidable-types
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.integers
open import elementary-number-theory.modular-arithmetic
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.prime-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.decidable-equality
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.transport-along-identifications

open import univalent-combinatorics.fibers-of-maps
```

</details>

## Idea

The **Legendre Symbol** is a function which determines whether or not an integer
is a perfect square in `ℤₚ` (i.e. whether or not it is a quadratic residue).
Specifically, let `p : ℕ` be a natural and `a : ℤ` be an integer. If `a` is a
square in `ℤₚ` then `legendre(p,a) = 1`. Similarly if `a` is not a square in
`ℤₚ` then `legendre(p,a) = -1`. Finally if `a` is congruent to `0` in `ℤₚ` then
`legendre(p,a) = 0`. Typically `p` is taken to be prime.

## Natural Numbers

### Definition for squareness in ℕ

```agda
is-square-ℕ : ℕ → UU lzero
is-square-ℕ n = Σ ℕ (λ x → n ＝ square-ℕ x)
```

### n > √n for n > 1

The idea is to assume `n = m + 2 ≤ sqrt(m + 2)` for some `m : ℕ` and derive a
contradiction by squaring both sides of the inequality

```agda
greater-than-square-root-ℕ :
  (n root : ℕ) → ¬ ((n +ℕ 2 ≤-ℕ root) × (n +ℕ 2 ＝ square-ℕ root))
greater-than-square-root-ℕ n root (pf-leq , pf-eq) =
  reflects-order-add-ℕ
    ( square-ℕ root)
    ( n *ℕ (n +ℕ 2) +ℕ n +ℕ 2)
    0
    ( tr
      ( leq-ℕ (n *ℕ (n +ℕ 2) +ℕ n +ℕ 2 +ℕ square-ℕ root))
      ( inv (left-unit-law-add-ℕ (square-ℕ root)))
      ( concatenate-eq-leq-ℕ
        ( square-ℕ root)
        ( inv
          ( helper ∙
            ( ap
              ( add-ℕ (n *ℕ (n +ℕ 2) +ℕ n +ℕ 2))
              pf-eq)))
        ( preserves-leq-mul-ℕ (n +ℕ 2) root (n +ℕ 2) root pf-leq pf-leq)))
  where
  helper : square-ℕ (n +ℕ 2) ＝ n *ℕ (n +ℕ 2) +ℕ n +ℕ 2 +ℕ n +ℕ 2
  helper =
    equational-reasoning
    square-ℕ (n +ℕ 2)
    ＝ n *ℕ (n +ℕ 2) +ℕ (2 *ℕ (n +ℕ 2))
      by (right-distributive-mul-add-ℕ n 2 (n +ℕ 2))
    ＝ n *ℕ (n +ℕ 2) +ℕ 2 *ℕ n +ℕ 4
      by
        ( ap
          ( add-ℕ (n *ℕ (n +ℕ 2)))
          ( left-distributive-mul-add-ℕ 2 n 2))
    ＝ n *ℕ (n +ℕ 2) +ℕ (n +ℕ 2 +ℕ (n +ℕ 2))
      by
        ( ap
          ( add-ℕ (n *ℕ (n +ℕ 2)))
          ( equational-reasoning
            2 *ℕ n +ℕ 4
            ＝ 4 +ℕ 2 *ℕ n
              by (commutative-add-ℕ (2 *ℕ n) 4)
            ＝ 2 +ℕ 2 +ℕ (n +ℕ n)
              by
                ( ap
                  ( add-ℕ 4)
                  ( left-two-law-mul-ℕ n))
            ＝ (2 +ℕ 2 +ℕ n) +ℕ n
              by
                ( inv
                  ( associative-add-ℕ 4 n n))
            ＝ n +ℕ (2 +ℕ 2 +ℕ n)
              by (commutative-add-ℕ (2 +ℕ 2 +ℕ n) n)
            ＝ n +ℕ (2 +ℕ (2 +ℕ n))
              by
                ( ap
                  ( add-ℕ n)
                  ( associative-add-ℕ 2 2 n))
            ＝ n +ℕ (2 +ℕ (n +ℕ 2))
              by
                ( ap-add-ℕ {n} {2 +ℕ (2 +ℕ n)}
                  refl
                  ( ap
                    ( add-ℕ 2)
                    ( commutative-add-ℕ 2 n)))
            ＝ n +ℕ 2 +ℕ (n +ℕ 2)
              by
                ( inv
                  ( associative-add-ℕ n 2 (n +ℕ 2)))))
    ＝ n *ℕ (n +ℕ 2) +ℕ n +ℕ 2 +ℕ (n +ℕ 2)
      by
        ( inv
          ( associative-add-ℕ
            ( n *ℕ (n +ℕ 2))
            ( n +ℕ 2)
            ( n +ℕ 2)))
```

### Squareness in ℕ is decidable

```agda
is-decidable-big-root :
  (n : ℕ) → is-decidable (Σ ℕ (λ root → (n ≤-ℕ root) × (n ＝ square-ℕ root)))
is-decidable-big-root 0 = inl (0 , star , refl)
is-decidable-big-root 1 = inl (1 , star , refl)
is-decidable-big-root (succ-ℕ (succ-ℕ n)) =
  inr (λ H → greater-than-square-root-ℕ n (pr1 H) (pr2 H))

is-decidable-square-ℕ : (n : ℕ) → is-decidable (is-square-ℕ n)
is-decidable-square-ℕ n =
  is-decidable-Σ-ℕ n
    ( λ x → n ＝ square-ℕ x)
    ( λ x → has-decidable-equality-ℕ n (square-ℕ x))
    ( is-decidable-big-root n)
```

## Integers

### Definitions for squareness in ℤ

```agda
square-ℤ : ℤ → ℤ
square-ℤ a = mul-ℤ a a

is-square-ℤ : ℤ → UU lzero
is-square-ℤ a = Σ ℤ (λ x → a ＝ square-ℤ x)
```

### Squares in ℤ are nonnegative

```agda
is-decidable-nonnegative-square-ℤ :
  (a : ℤ) →
  (is-nonnegative-ℤ a) + (is-nonnegative-ℤ (neg-ℤ a)) →
  is-nonnegative-ℤ (square-ℤ a)
is-decidable-nonnegative-square-ℤ _ (inl x) = is-nonnegative-mul-ℤ x x
is-decidable-nonnegative-square-ℤ a (inr x) =
  tr
    is-nonnegative-ℤ
    ( double-negative-law-mul-ℤ a a)
    ( is-nonnegative-mul-ℤ x x)

is-nonnegative-square-ℤ : (a : ℤ) → is-nonnegative-ℤ (square-ℤ a)
is-nonnegative-square-ℤ a =
  is-decidable-nonnegative-square-ℤ a decide-is-nonnegative-ℤ
```

### The squares in ℤ are exactly the squares in ℕ

```agda
is-square-int-if-is-square-nat : {n : ℕ} → is-square-ℕ n → is-square-ℤ (int-ℕ n)
is-square-int-if-is-square-nat (root , pf-square) =
  ( pair
    ( int-ℕ root)
    ( ( ap int-ℕ pf-square) ∙
      ( inv (mul-int-ℕ root root))))

is-square-nat-if-is-square-int : {a : ℤ} → is-square-ℤ a → is-square-ℕ (abs-ℤ a)
is-square-nat-if-is-square-int (root , pf-square) =
  ( pair
    ( abs-ℤ root)
    ( ( ap abs-ℤ pf-square) ∙
      ( multiplicative-abs-ℤ root root)))

is-nat-square-iff-is-int-square :
  (n : ℕ) → is-square-ℕ n ↔ is-square-ℤ (int-ℕ n)
pr1 (is-nat-square-iff-is-int-square n) = is-square-int-if-is-square-nat
pr2 (is-nat-square-iff-is-int-square n) H =
  tr is-square-ℕ (abs-int-ℕ n) (is-square-nat-if-is-square-int H)

is-int-square-iff-nonneg-nat-square :
  (a : ℤ) → is-square-ℤ a ↔ is-nonnegative-ℤ a × is-square-ℕ (abs-ℤ a)
pr1 (is-int-square-iff-nonneg-nat-square a) (root , pf-square) =
  ( pair
    ( tr is-nonnegative-ℤ (inv pf-square) (is-nonnegative-square-ℤ root))
    ( is-square-nat-if-is-square-int (root , pf-square)))
pr2 (is-int-square-iff-nonneg-nat-square a) (pf-nonneg , (root , pf-square)) =
  ( pair
    ( int-ℕ root)
    ( ( inv (int-abs-is-nonnegative-ℤ a pf-nonneg)) ∙
      ( pr2 (is-square-int-if-is-square-nat (root , pf-square)))))
```

### Squareness in ℤ is decidable

```agda
is-decidable-square-ℤ : (a : ℤ) → is-decidable (is-square-ℤ a)
is-decidable-square-ℤ (inl n) =
  inr (map-neg (pr1 (is-int-square-iff-nonneg-nat-square (inl n))) pr1)
is-decidable-square-ℤ (inr (inl n)) =
  inl (zero-ℤ , refl)
is-decidable-square-ℤ (inr (inr n)) =
  is-decidable-iff
    is-square-int-if-is-square-nat
    is-square-nat-if-is-square-int
    ( is-decidable-square-ℕ (succ-ℕ n))
```

## ℤₚ

### Definitions for squareness in ℤₚ

```agda
square-ℤ-Mod : (p : ℕ) → ℤ-Mod p → ℤ-Mod p
square-ℤ-Mod 0 a = mul-ℤ a a
square-ℤ-Mod (succ-ℕ p) a = mul-ℤ-Mod (succ-ℕ p) a a

is-square-ℤ-Mod : (p : ℕ) → ℤ-Mod p → UU lzero
is-square-ℤ-Mod 0 k = is-square-ℤ k
is-square-ℤ-Mod (succ-ℕ p) k =
  Σ (ℤ-Mod (succ-ℕ p)) (λ x → square-ℤ-Mod (succ-ℕ p) x ＝ k)
```

### Squareness in ℤₚ is decidable

```agda
is-decidable-square-ℤ-Mod :
  (p : ℕ) (k : ℤ-Mod p) → is-decidable (is-square-ℤ-Mod p k)
is-decidable-square-ℤ-Mod 0 k = is-decidable-square-ℤ k
is-decidable-square-ℤ-Mod (succ-ℕ p) k =
  is-decidable-fiber-Fin {succ-ℕ p} {succ-ℕ p} (square-ℤ-Mod (succ-ℕ p)) k
```

## Legendre Symbol

### Definitions for the Legendre Symbol

```agda
int-is-square-ℤ-Mod :
  {p : ℕ} {k : ℤ-Mod p} →
  is-decidable (is-zero-ℤ-Mod p k) →
  is-decidable (is-square-ℤ-Mod p k) →
  ℤ
int-is-square-ℤ-Mod (inl _) _ = zero-ℤ
int-is-square-ℤ-Mod (inr _) (inl _) = one-ℤ
int-is-square-ℤ-Mod (inr _) (inr _) = neg-one-ℤ

legendre : ℕ → ℤ → ℤ
legendre p a =
  int-is-square-ℤ-Mod
    ( has-decidable-equality-ℤ-Mod p arg-mod-p (zero-ℤ-Mod p))
    ( is-decidable-square-ℤ-Mod p arg-mod-p)
  where
  arg-mod-p : ℤ-Mod p
  arg-mod-p = mod-ℤ p a
```
