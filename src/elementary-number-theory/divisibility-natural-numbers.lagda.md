---
title: Divisibility of natural numbers
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module elementary-number-theory.divisibility-natural-numbers where

open import elementary-number-theory.addition-natural-numbers using
  ( add-ℕ; ap-add-ℕ; is-injective-add-ℕ'; commutative-add-ℕ)
open import elementary-number-theory.distance-natural-numbers using
  ( dist-ℕ; is-additive-right-inverse-dist-ℕ)
open import elementary-number-theory.equality-natural-numbers using
  ( is-decidable-is-zero-ℕ)
open import elementary-number-theory.inequality-natural-numbers using
  ( leq-ℕ; leq-leq-mul-ℕ'; concatenate-eq-leq-eq-ℕ; leq-add-ℕ'; le-ℕ;
    contradiction-le-ℕ; concatenate-leq-eq-ℕ; leq-mul-ℕ')
open import elementary-number-theory.multiplication-natural-numbers using
  ( mul-ℕ; mul-ℕ'; commutative-mul-ℕ; right-unit-law-mul-ℕ; left-zero-law-mul-ℕ;
    right-distributive-mul-add-ℕ; right-zero-law-mul-ℕ; left-unit-law-mul-ℕ;
    is-one-right-is-one-mul-ℕ; is-one-is-left-unit-mul-ℕ; associative-mul-ℕ;
    is-injective-mul-ℕ; is-emb-mul-ℕ'; is-nonzero-left-factor-mul-ℕ;
    is-injective-mul-ℕ')
open import elementary-number-theory.natural-numbers using
  ( ℕ; zero-ℕ; succ-ℕ; is-zero-ℕ; is-one-ℕ; is-nonzero-ℕ;
    is-successor-is-nonzero-ℕ)

open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.empty-types using (ex-falso)
open import foundation.equational-reasoning
open import foundation.identity-types using (_＝_; refl; _∙_; inv; tr; ap)
open import foundation.negation using (¬)
open import foundation.propositional-maps using (is-prop-map-is-emb)
open import foundation.propositions using (is-prop)
open import foundation.universe-levels using (UU; lzero)
```

# Divisibility on the natural numbers

```agda
div-ℕ : ℕ → ℕ → UU lzero
div-ℕ m n = Σ ℕ (λ k → mul-ℕ k m ＝ n)

quotient-div-ℕ : (x y : ℕ) → div-ℕ x y → ℕ
quotient-div-ℕ x y H = pr1 H

eq-quotient-div-ℕ :
  (x y : ℕ) (H : div-ℕ x y) → mul-ℕ (quotient-div-ℕ x y H) x ＝ y
eq-quotient-div-ℕ x y H = pr2 H

eq-quotient-div-ℕ' :
  (x y : ℕ) (H : div-ℕ x y) → mul-ℕ x (quotient-div-ℕ x y H) ＝ y
eq-quotient-div-ℕ' x y H =
  commutative-mul-ℕ x (quotient-div-ℕ x y H) ∙ eq-quotient-div-ℕ x y H

concatenate-eq-div-ℕ :
  {x y z : ℕ} → x ＝ y → div-ℕ y z → div-ℕ x z
concatenate-eq-div-ℕ refl p = p

concatenate-div-eq-ℕ :
  {x y z : ℕ} → div-ℕ x y → y ＝ z → div-ℕ x z
concatenate-div-eq-ℕ p refl = p

concatenate-eq-div-eq-ℕ :
  {x y z w : ℕ} → x ＝ y → div-ℕ y z → z ＝ w → div-ℕ x w
concatenate-eq-div-eq-ℕ refl p refl = p

is-even-ℕ : ℕ → UU lzero
is-even-ℕ n = div-ℕ 2 n

is-odd-ℕ : ℕ → UU lzero
is-odd-ℕ n = ¬ (is-even-ℕ n)

div-one-ℕ :
  (x : ℕ) → div-ℕ 1 x
pr1 (div-one-ℕ x) = x
pr2 (div-one-ℕ x) = right-unit-law-mul-ℕ x

div-is-one-ℕ :
  (k x : ℕ) → is-one-ℕ k → div-ℕ k x
div-is-one-ℕ .1 x refl = div-one-ℕ x

div-zero-ℕ :
  (k : ℕ) → div-ℕ k 0
pr1 (div-zero-ℕ k) = 0
pr2 (div-zero-ℕ k) = left-zero-law-mul-ℕ k

div-is-zero-ℕ :
  (k x : ℕ) → is-zero-ℕ x → div-ℕ k x
div-is-zero-ℕ k .zero-ℕ refl = div-zero-ℕ k
```

## Divisibility by a nonzero natural number is a property

```agda
is-prop-div-ℕ : (k x : ℕ) → is-nonzero-ℕ k → is-prop (div-ℕ k x)
is-prop-div-ℕ k x f = is-prop-map-is-emb (is-emb-mul-ℕ' k f) x
```

## A three-for-two property of division

```agda
div-add-ℕ :
  (d x y : ℕ) → div-ℕ d x → div-ℕ d y → div-ℕ d (add-ℕ x y)
pr1 (div-add-ℕ d x y (pair n p) (pair m q)) = add-ℕ n m
pr2 (div-add-ℕ d x y (pair n p) (pair m q)) =
  ( right-distributive-mul-add-ℕ n m d) ∙
  ( ap-add-ℕ p q)

div-left-summand-ℕ :
  (d x y : ℕ) → div-ℕ d y → div-ℕ d (add-ℕ x y) → div-ℕ d x
div-left-summand-ℕ zero-ℕ x y (pair m q) (pair n p) =
  pair zero-ℕ
    ( ( inv (right-zero-law-mul-ℕ n)) ∙
      ( p ∙ (ap (add-ℕ x) ((inv q) ∙ (right-zero-law-mul-ℕ m)))))
pr1 (div-left-summand-ℕ (succ-ℕ d) x y (pair m q) (pair n p)) = dist-ℕ m n
pr2 (div-left-summand-ℕ (succ-ℕ d) x y (pair m q) (pair n p)) =
  is-injective-add-ℕ' (mul-ℕ m (succ-ℕ d))
    ( ( inv
        ( ( right-distributive-mul-add-ℕ m (dist-ℕ m n) (succ-ℕ d)) ∙
          ( commutative-add-ℕ
            ( mul-ℕ m (succ-ℕ d))
            ( mul-ℕ (dist-ℕ m n) (succ-ℕ d))))) ∙
      ( ( ap
          ( mul-ℕ' (succ-ℕ d))
          ( is-additive-right-inverse-dist-ℕ m n
            ( leq-leq-mul-ℕ' m n d
              ( concatenate-eq-leq-eq-ℕ q
                ( leq-add-ℕ' y x)
                ( inv p))))) ∙
        ( p ∙ (ap (add-ℕ x) (inv q)))))

div-right-summand-ℕ :
  (d x y : ℕ) → div-ℕ d x → div-ℕ d (add-ℕ x y) → div-ℕ d y
div-right-summand-ℕ d x y H1 H2 =
  div-left-summand-ℕ d y x H1 (concatenate-div-eq-ℕ H2 (commutative-add-ℕ x y))
```

### If `x < d` and `d | x` then `x ＝ 0`

```agda
is-zero-div-ℕ :
  (d x : ℕ) → le-ℕ x d → div-ℕ d x → is-zero-ℕ x
is-zero-div-ℕ d zero-ℕ H D = refl
is-zero-div-ℕ d (succ-ℕ x) H (pair (succ-ℕ k) p) =
  ex-falso
    ( contradiction-le-ℕ
      ( succ-ℕ x) d H
      ( concatenate-leq-eq-ℕ d
        ( leq-add-ℕ' d (mul-ℕ k d)) p))
```

### The divisibility relation is a partial order on the natural numbers

```agda
refl-div-ℕ : (x : ℕ) → div-ℕ x x
pr1 (refl-div-ℕ x) = 1
pr2 (refl-div-ℕ x) = left-unit-law-mul-ℕ x

antisymmetric-div-ℕ :
  (x y : ℕ) → div-ℕ x y → div-ℕ y x → x ＝ y
antisymmetric-div-ℕ zero-ℕ zero-ℕ H K = refl
antisymmetric-div-ℕ zero-ℕ (succ-ℕ y) (pair k p) K =
  inv (right-zero-law-mul-ℕ k) ∙ p
antisymmetric-div-ℕ (succ-ℕ x) zero-ℕ H (pair l q) =
  inv q ∙ right-zero-law-mul-ℕ l
antisymmetric-div-ℕ (succ-ℕ x) (succ-ℕ y) (pair k p) (pair l q) =
  ( inv (left-unit-law-mul-ℕ (succ-ℕ x))) ∙
  ( ( ap ( mul-ℕ' (succ-ℕ x))
         ( inv
           ( is-one-right-is-one-mul-ℕ l k
             ( is-one-is-left-unit-mul-ℕ (mul-ℕ l k) x
               ( ( associative-mul-ℕ l k (succ-ℕ x)) ∙
                 ( ap (mul-ℕ l) p ∙ q)))))) ∙
    ( p))

transitive-div-ℕ :
  (x y z : ℕ) → div-ℕ x y → div-ℕ y z → div-ℕ x z
pr1 (transitive-div-ℕ x y z (pair k p) (pair l q)) = mul-ℕ l k
pr2 (transitive-div-ℕ x y z (pair k p) (pair l q)) =
  associative-mul-ℕ l k x ∙ (ap (mul-ℕ l) p ∙ q)
```

### If `b` divides `a` and `c` divides `b` and `c` is nonzero, then `a/b · b/c ＝ a/c`

```agda
simplify-mul-quotient-div-ℕ :
  {a b c : ℕ}  → is-nonzero-ℕ c → (H : div-ℕ b a) (K : div-ℕ c b) → 
  ( mul-ℕ (quotient-div-ℕ b a H) (quotient-div-ℕ c b K)) ＝
  ( quotient-div-ℕ c a (transitive-div-ℕ c b a K H))
simplify-mul-quotient-div-ℕ {a} {b} {c} nz H K =
  is-injective-mul-ℕ' c nz
    ( equational-reasoning
      mul-ℕ (mul-ℕ a/b b/c) c 
      ＝ mul-ℕ a/b (mul-ℕ b/c c) by associative-mul-ℕ a/b b/c c
      ＝ mul-ℕ a/b b             by ap (mul-ℕ a/b) (eq-quotient-div-ℕ c b K)
      ＝ a                       by eq-quotient-div-ℕ b a H
      ＝ mul-ℕ a/c c             by inv
                                      ( eq-quotient-div-ℕ c a
                                        ( transitive-div-ℕ c b a K H)))
  where
  a/b : ℕ
  a/b = quotient-div-ℕ b a H
  b/c : ℕ
  b/c = quotient-div-ℕ c b K
  a/c : ℕ
  a/c = quotient-div-ℕ c a (transitive-div-ℕ c b a K H)
```

### If `x` divides `y` then `x` divides any multiple of `y`

```agda
div-mul-ℕ :
  (k x y : ℕ) → div-ℕ x y → div-ℕ x (mul-ℕ k y)
div-mul-ℕ k x y H =
  transitive-div-ℕ x y (mul-ℕ k y) H (pair k refl)

div-mul-ℕ' :
  (k x y : ℕ) → div-ℕ x y → div-ℕ x (mul-ℕ y k)
div-mul-ℕ' k x y H =
  tr (div-ℕ x) (commutative-mul-ℕ k y) (div-mul-ℕ k x y H)
```

### Multiplication preserves divisibility

```agda
preserves-div-mul-ℕ :
  (k x y : ℕ) → div-ℕ x y → div-ℕ (mul-ℕ k x) (mul-ℕ k y)
pr1 (preserves-div-mul-ℕ k x y (pair q p)) = q
pr2 (preserves-div-mul-ℕ k x y (pair q p)) =
  ( inv (associative-mul-ℕ q k x)) ∙
    ( ( ap (mul-ℕ' x) (commutative-mul-ℕ q k)) ∙
      ( ( associative-mul-ℕ k q x) ∙
        ( ap (mul-ℕ k) p)))
```

### Multiplication by a nonzero number reflects divisibility

```agda
reflects-div-mul-ℕ :
  (k x y : ℕ) → is-nonzero-ℕ k → div-ℕ (mul-ℕ k x) (mul-ℕ k y) → div-ℕ x y
pr1 (reflects-div-mul-ℕ k x y H (pair q p)) = q
pr2 (reflects-div-mul-ℕ k x y H (pair q p)) =
  is-injective-mul-ℕ k H
    ( ( inv (associative-mul-ℕ k q x)) ∙
      ( ( ap (mul-ℕ' x) (commutative-mul-ℕ k q)) ∙
        ( ( associative-mul-ℕ q k x) ∙
          ( p))))
```

### If a nonzero number `d` divides `y`, then `dx` divides `y` if and only if `x` divides the quotient `y/d`.

```agda
div-quotient-div-div-ℕ :
  (x y d : ℕ) (H : div-ℕ d y) → is-nonzero-ℕ d →
  div-ℕ (mul-ℕ d x) y → div-ℕ x (quotient-div-ℕ d y H)
div-quotient-div-div-ℕ x y d H f K =
  reflects-div-mul-ℕ d x
    ( quotient-div-ℕ d y H)
    ( f)
    ( tr (div-ℕ (mul-ℕ d x)) (inv (eq-quotient-div-ℕ' d y H)) K)

div-div-quotient-div-ℕ :
  (x y d : ℕ) (H : div-ℕ d y) →
  div-ℕ x (quotient-div-ℕ d y H) → div-ℕ (mul-ℕ d x) y
div-div-quotient-div-ℕ x y d H K =
  tr ( div-ℕ (mul-ℕ d x))
     ( eq-quotient-div-ℕ' d y H)
     ( preserves-div-mul-ℕ d x (quotient-div-ℕ d y H) K)
```

### Suppose `H : b | a` and `K : c | b`, where `c` is nonzero`. If `d` divides `b/c` then `d` divides `a/c`.

```agda
div-quotient-div-div-quotient-div-ℕ :
  (a b c d : ℕ) → is-nonzero-ℕ c → (H : div-ℕ b a) (K : div-ℕ c b) →
  div-ℕ d (quotient-div-ℕ c b K) →
  div-ℕ d (quotient-div-ℕ c a (transitive-div-ℕ c b a K H))
div-quotient-div-div-quotient-div-ℕ a b c d nz H K L =
  tr
    ( div-ℕ d)
    ( simplify-mul-quotient-div-ℕ nz H K)
    ( div-mul-ℕ
      ( quotient-div-ℕ b a H)
      ( d)
      ( quotient-div-ℕ c b K)
      ( L))
```

### `0 | x` implies `x = 0` and `x | 1` implies `x = 1`

```agda
is-zero-div-zero-ℕ : (x : ℕ) → div-ℕ zero-ℕ x → is-zero-ℕ x
is-zero-div-zero-ℕ x H = antisymmetric-div-ℕ x zero-ℕ (div-zero-ℕ x) H

is-zero-is-zero-div-ℕ : (x y : ℕ) → div-ℕ x y → is-zero-ℕ x → is-zero-ℕ y
is-zero-is-zero-div-ℕ .zero-ℕ y d refl = is-zero-div-zero-ℕ y d

is-one-div-one-ℕ : (x : ℕ) → div-ℕ x 1 → is-one-ℕ x
is-one-div-one-ℕ x H = antisymmetric-div-ℕ x 1 H (div-one-ℕ x)

is-one-div-ℕ : (x y : ℕ) → div-ℕ x y → div-ℕ x (succ-ℕ y) → is-one-ℕ x
is-one-div-ℕ x y H K = is-one-div-one-ℕ x (div-right-summand-ℕ x y 1 H K)

div-eq-ℕ : (x y : ℕ) → x ＝ y → div-ℕ x y
div-eq-ℕ x .x refl = refl-div-ℕ x
```

```agda
leq-div-succ-ℕ : (d x : ℕ) → div-ℕ d (succ-ℕ x) → leq-ℕ d (succ-ℕ x)
leq-div-succ-ℕ d x (pair (succ-ℕ k) p) =
  concatenate-leq-eq-ℕ d (leq-mul-ℕ' k d) p

leq-div-ℕ : (d x : ℕ) → is-nonzero-ℕ x → div-ℕ d x → leq-ℕ d x
leq-div-ℕ d x f H with is-successor-is-nonzero-ℕ f
... | (pair y refl) = leq-div-succ-ℕ d y H
```

```agda
is-one-is-divisor-below-ℕ : ℕ → ℕ → UU lzero
is-one-is-divisor-below-ℕ n a =
  (x : ℕ) → leq-ℕ x n → div-ℕ x a → is-one-ℕ x
```

### If `d` divides a nonzero number `x`, then the quotient `x/d` is also nonzero

```agda
is-nonzero-quotient-div-ℕ :
  {d x : ℕ} (H : div-ℕ d x) →
  is-nonzero-ℕ x → is-nonzero-ℕ (quotient-div-ℕ d x H)
is-nonzero-quotient-div-ℕ {d} {.(mul-ℕ k d)} (pair k refl) =
  is-nonzero-left-factor-mul-ℕ k d
```
