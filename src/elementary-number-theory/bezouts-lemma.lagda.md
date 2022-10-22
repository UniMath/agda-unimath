---
title: Bezout's lemma
---

```agda
module elementary-number-theory.bezouts-lemma where

open import elementary-number-theory.absolute-value-integers using 
 ( abs-ℤ; abs-int-ℕ; abs-neg-ℤ; int-abs-is-nonnegative-ℤ; is-nonzero-abs-ℤ; multiplicative-abs-ℤ)
open import elementary-number-theory.addition-integers
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.congruence-integers
open import elementary-number-theory.difference-integers
open import elementary-number-theory.distance-integers
open import elementary-number-theory.distance-natural-numbers
open import elementary-number-theory.divisibility-modular-arithmetic
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.divisibility-integers
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.euclidean-division-natural-numbers
open import elementary-number-theory.greatest-common-divisor-natural-numbers
open import elementary-number-theory.greatest-common-divisor-integers
open import elementary-number-theory.inequality-integers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.integers
open import elementary-number-theory.lower-bounds-natural-numbers
open import elementary-number-theory.modular-arithmetic
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.multiplication-integers 
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.well-ordering-principle-natural-numbers

open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.decidable-maps
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equational-reasoning
open import foundation.identity-types
open import foundation.negation
open import foundation.unit-type
open import foundation.universe-levels

open import univalent-combinatorics.standard-finite-types
```

## Idea

Bezout's lemma shows that for any two natural numbers `x` and `y` there exist `k` and `l` such that `dist-ℕ (kx,ly) = gcd(x,y)`. To prove this, note that the predicate `P : ℕ → UU lzero` given by

```md
  P z := Σ (k : ℕ), Σ (l : ℕ), dist-ℕ (kx, ly) = z
```

is decidable, because `P z ⇔ [y]_x | [z]_x` in `ℤ/x`. The least positive `z` such that `P z` holds is `gcd x y`.

## Definitions

```agda
is-distance-between-multiples-ℕ : ℕ → ℕ → ℕ → UU lzero
is-distance-between-multiples-ℕ x y z =
  Σ ℕ (λ k → Σ ℕ (λ l → dist-ℕ (mul-ℕ k x) (mul-ℕ l y) ＝ z))

is-distance-between-multiples-fst-coeff-ℕ : {x y z : ℕ} → is-distance-between-multiples-ℕ x y z → ℕ
is-distance-between-multiples-fst-coeff-ℕ dist = pr1 dist

is-distance-between-multiples-snd-coeff-ℕ : {x y z : ℕ} → is-distance-between-multiples-ℕ x y z → ℕ
is-distance-between-multiples-snd-coeff-ℕ dist = pr1 (pr2 dist)

is-distance-between-multiples-eqn-ℕ : {x y z : ℕ} 
  → (d : is-distance-between-multiples-ℕ x y z) 
  → dist-ℕ ( mul-ℕ (is-distance-between-multiples-fst-coeff-ℕ d) x) 
    ( mul-ℕ (is-distance-between-multiples-snd-coeff-ℕ d) y) ＝ z
is-distance-between-multiples-eqn-ℕ dist = pr2 (pr2 dist)

is-distance-between-multiples-sym-ℕ : (x y z : ℕ)
  → is-distance-between-multiples-ℕ x y z → is-distance-between-multiples-ℕ y x z
is-distance-between-multiples-sym-ℕ x y z (pair k (pair l eqn)) = 
  pair l (pair k (symmetric-dist-ℕ (mul-ℕ l y) (mul-ℕ k x) ∙ eqn))
```

## Lemmas

### If `z = dist-ℕ (kx, ly)` for some `k` and `l`, then `[y] | [z]` in `ℤ-Mod x`

If `z = dist-ℕ (kx, ly)` for some `k` and `l`, then it follows that `ly ≡ ±z mod x`. It follows that `±ly ≡ z mod x`, and therefore that `[y] | [z]` in `ℤ-Mod x`

```agda
int-is-distance-between-multiples-ℕ : 
  (x y z : ℕ) → (d : is-distance-between-multiples-ℕ x y z)
  → (H : leq-ℕ 
    (mul-ℕ (is-distance-between-multiples-fst-coeff-ℕ d) x) 
    (mul-ℕ (is-distance-between-multiples-snd-coeff-ℕ d) y))
  → add-ℤ (int-ℕ z)  
    (mul-ℤ 
      (int-ℕ (is-distance-between-multiples-fst-coeff-ℕ d))
      (int-ℕ x))
    ＝ mul-ℤ 
      (int-ℕ (is-distance-between-multiples-snd-coeff-ℕ d)) 
      (int-ℕ y)
int-is-distance-between-multiples-ℕ x y z (k , l , p) H =
  equational-reasoning
    add-ℤ (int-ℕ z) (mul-ℤ (int-ℕ k) (int-ℕ x))
    ＝ add-ℤ (int-ℕ z) (int-ℕ (mul-ℕ k x))
      by ap (λ p → add-ℤ (int-ℕ z) p) (mul-int-ℕ k x) 
    ＝ int-ℕ (add-ℕ z (mul-ℕ k x)) 
      by add-int-ℕ z (mul-ℕ k x) 
    ＝ int-ℕ (mul-ℕ l y) 
      by ap (int-ℕ) 
        (rewrite-left-dist-add-ℕ z (mul-ℕ k x) (mul-ℕ l y) H (inv p))
    ＝ mul-ℤ (int-ℕ l) (int-ℕ y)
      by inv (mul-int-ℕ l y)

div-mod-is-distance-between-multiples-ℕ :
  (x y z : ℕ) →
  is-distance-between-multiples-ℕ x y z → div-ℤ-Mod x (mod-ℕ x y) (mod-ℕ x z)
div-mod-is-distance-between-multiples-ℕ x y z (k , l , p) 
  with decide-leq-ℕ (mul-ℕ k x) (mul-ℕ l y)
... | inl kxly = (mod-ℕ x l , 
  (equational-reasoning
    mul-ℤ-Mod x (mod-ℕ x l) (mod-ℕ x y)
    ＝ mul-ℤ-Mod x (mod-ℤ x (int-ℕ l)) (mod-ℕ x y) 
      by inv (ap (λ p → mul-ℤ-Mod x p (mod-ℕ x y)) (mod-int-ℕ x l))
    ＝ mul-ℤ-Mod x (mod-ℤ x (int-ℕ l)) (mod-ℤ x (int-ℕ y))
      by inv (ap (λ p → mul-ℤ-Mod x (mod-ℤ x (int-ℕ l)) p) (mod-int-ℕ x y))
    ＝ mod-ℤ x (mul-ℤ (int-ℕ l) (int-ℕ y)) 
      by inv (preserves-mul-mod-ℤ x (int-ℕ l) (int-ℕ y)) 
    ＝ mod-ℤ x (add-ℤ (int-ℕ z) (mul-ℤ (int-ℕ k) (int-ℕ x)))
      by inv (ap (mod-ℤ x) 
        (int-is-distance-between-multiples-ℕ x y z (k , l , p) kxly))
    ＝ add-ℤ-Mod x (mod-ℤ x (int-ℕ z)) 
      (mod-ℤ x (mul-ℤ (int-ℕ k) (int-ℕ x)))
      by preserves-add-mod-ℤ x (int-ℕ z) (mul-ℤ (int-ℕ k) (int-ℕ x)) 
    ＝ add-ℤ-Mod x (mod-ℤ x (int-ℕ z))
      (mul-ℤ-Mod x (mod-ℤ x (int-ℕ k)) (mod-ℤ x (int-ℕ x)))
      by ap (λ p → add-ℤ-Mod x (mod-ℤ x (int-ℕ z)) p)
        (preserves-mul-mod-ℤ x (int-ℕ k) (int-ℕ x))
    ＝ add-ℤ-Mod x (mod-ℤ x (int-ℕ z))
      (mul-ℤ-Mod x (mod-ℤ x (int-ℕ k)) (mod-ℤ x zero-ℤ))
      by ap (λ p → add-ℤ-Mod x (mod-ℤ x (int-ℕ z)) 
        (mul-ℤ-Mod x (mod-ℤ x (int-ℕ k)) p)) 
        (mod-int-ℕ x x ∙ (mod-refl-ℕ x ∙ inv (mod-zero-ℤ x))) 
    ＝ add-ℤ-Mod x (mod-ℤ x (int-ℕ z))
      (mod-ℤ x (mul-ℤ (int-ℕ k) zero-ℤ)) 
      by ap (λ p → add-ℤ-Mod x (mod-ℤ x (int-ℕ z)) p)
        (inv (preserves-mul-mod-ℤ x (int-ℕ k) zero-ℤ))
    ＝ add-ℤ-Mod x (mod-ℤ x (int-ℕ z)) (mod-ℤ x zero-ℤ)
      by ap (λ p → add-ℤ-Mod x (mod-ℤ x (int-ℕ z)) (mod-ℤ x p))
        (right-zero-law-mul-ℤ (int-ℕ k))
    ＝ mod-ℤ x (add-ℤ (int-ℕ z) zero-ℤ)
      by inv (preserves-add-mod-ℤ x (int-ℕ z) zero-ℤ)
    ＝ mod-ℤ x (int-ℕ z)
      by ap (mod-ℤ x) (right-unit-law-add-ℤ (int-ℕ z))
    ＝ mod-ℕ x z by mod-int-ℕ x z
  ))
... | inr lykx = (mod-ℤ x (neg-ℤ (int-ℕ l)) , 
  (equational-reasoning
    mul-ℤ-Mod x (mod-ℤ x (neg-ℤ (int-ℕ l))) (mod-ℕ x y)
    ＝ mul-ℤ-Mod x (mod-ℤ x (neg-ℤ (int-ℕ l))) (mod-ℤ x (int-ℕ y)) 
      by inv (ap (λ p → mul-ℤ-Mod x (mod-ℤ x (neg-ℤ (int-ℕ l))) p) 
        (mod-int-ℕ x y)) 
    ＝ mod-ℤ x (mul-ℤ (neg-ℤ (int-ℕ l)) (int-ℕ y))
      by inv (preserves-mul-mod-ℤ x (neg-ℤ (int-ℕ l)) (int-ℕ y))
    ＝ mod-ℤ x (add-ℤ (mul-ℤ (neg-ℤ (int-ℕ l)) (int-ℕ y)) zero-ℤ)
      by ap (mod-ℤ x) 
        (inv (right-unit-law-add-ℤ (mul-ℤ (neg-ℤ (int-ℕ l)) (int-ℕ y))))
    ＝ add-ℤ-Mod x (mod-ℤ x (mul-ℤ (neg-ℤ (int-ℕ l)) (int-ℕ y)))
        (mod-ℤ x zero-ℤ)
      by preserves-add-mod-ℤ x (mul-ℤ (neg-ℤ (int-ℕ l)) (int-ℕ y)) (zero-ℤ)
    ＝ add-ℤ-Mod x (mod-ℤ x (mul-ℤ (neg-ℤ (int-ℕ l)) (int-ℕ y)))
        (mod-ℤ x (mul-ℤ (int-ℕ k) zero-ℤ))
      by ap (λ p → add-ℤ-Mod x 
        (mod-ℤ x (mul-ℤ (neg-ℤ (int-ℕ l)) (int-ℕ y))) (mod-ℤ x p))
        (inv (right-zero-law-mul-ℤ (int-ℕ k)))
    ＝ add-ℤ-Mod x (mod-ℤ x (mul-ℤ (neg-ℤ (int-ℕ l)) (int-ℕ y)))
        (mul-ℤ-Mod x (mod-ℤ x (int-ℕ k)) (mod-ℤ x zero-ℤ))
      by ap (λ p → add-ℤ-Mod x 
        (mod-ℤ x (mul-ℤ (neg-ℤ (int-ℕ l)) (int-ℕ y))) p)
        (preserves-mul-mod-ℤ x (int-ℕ k) zero-ℤ)
    ＝ add-ℤ-Mod x (mod-ℤ x (mul-ℤ (neg-ℤ (int-ℕ l)) (int-ℕ y)))
        (mul-ℤ-Mod x (mod-ℤ x (int-ℕ k)) (mod-ℤ x (int-ℕ x)))
      by ap (λ p → add-ℤ-Mod x
        (mod-ℤ x (mul-ℤ (neg-ℤ (int-ℕ l)) (int-ℕ y)))
        (mul-ℤ-Mod x (mod-ℤ x (int-ℕ k)) p))
        (mod-zero-ℤ x ∙ (inv (mod-refl-ℕ x) ∙ inv (mod-int-ℕ x x)))
    ＝ add-ℤ-Mod x (mod-ℤ x (mul-ℤ (neg-ℤ (int-ℕ l)) (int-ℕ y)))
        (mod-ℤ x (mul-ℤ (int-ℕ k) (int-ℕ x)))
      by ap (λ p → add-ℤ-Mod x 
        (mod-ℤ x (mul-ℤ (neg-ℤ (int-ℕ l)) (int-ℕ y))) p) 
        (inv (preserves-mul-mod-ℤ x (int-ℕ k) (int-ℕ x)))
    ＝ mod-ℤ x (add-ℤ (mul-ℤ (neg-ℤ (int-ℕ l)) (int-ℕ y))
        (mul-ℤ (int-ℕ k) (int-ℕ x)))
      by inv (preserves-add-mod-ℤ x (mul-ℤ (neg-ℤ (int-ℕ l)) (int-ℕ y))
        (mul-ℤ (int-ℕ k) (int-ℕ x)))
    ＝ mod-ℤ x (int-ℕ z)
      by ap (mod-ℤ x) (equational-reasoning
        add-ℤ (mul-ℤ (neg-ℤ (int-ℕ l)) (int-ℕ y)) 
          (mul-ℤ (int-ℕ k) (int-ℕ x))
        ＝ add-ℤ (neg-ℤ (mul-ℤ (int-ℕ l) (int-ℕ y))) 
          (mul-ℤ (int-ℕ k) (int-ℕ x))
        by ap (λ p → add-ℤ p (mul-ℤ (int-ℕ k) (int-ℕ x)))
          (left-negative-law-mul-ℤ (int-ℕ l) (int-ℕ y))
        ＝ add-ℤ (mul-ℤ (int-ℕ k) (int-ℕ x)) 
           (neg-ℤ (mul-ℤ (int-ℕ l) (int-ℕ y)))
        by commutative-add-ℤ (neg-ℤ (mul-ℤ (int-ℕ l) (int-ℕ y))) 
          (mul-ℤ (int-ℕ k) (int-ℕ x))
        ＝ add-ℤ (add-ℤ (int-ℕ z) (mul-ℤ (int-ℕ l) (int-ℕ y))) 
          (neg-ℤ (mul-ℤ (int-ℕ l) (int-ℕ y)))
        by ap (λ p → add-ℤ p (neg-ℤ (mul-ℤ (int-ℕ l) (int-ℕ y))))
          (inv (int-is-distance-between-multiples-ℕ y x z 
            (is-distance-between-multiples-sym-ℕ x y z (k , l , p)) 
            lykx))
        ＝ int-ℕ z
        by isretr-add-neg-ℤ' (mul-ℤ (int-ℕ l) (int-ℕ y)) (int-ℕ z))
     ＝ mod-ℕ x z by mod-int-ℕ x z))

```

### If `[y] | [z]` in `ℤ-Mod x`, then `z = dist-ℕ (kx, ly)` for some `k` and `l`
If `x = 0`, then we can simply argue in `ℤ`. Otherwise, if `[y] | [z]` in `ℤ-Mod x`, there exists some equivalence class `u` in `ℤ-Mod x` such that `[u] [y] ≡ [z]` as a congruence mod `x`. This `u` can always be chosen such that `x > u ≥ 0`. Therefore, there exists some integer `a ≥ 0` such that `ax = uy - z`, or `ax = z - uy`. In the first case, we can extract the distance condition we desire. In the other case, we have that `ax + uy = z`. This can be written as `(a + y)x + (u - x)y = z`, so that the second term is non-positive. Then, in this case, we again can extract the distance condition we desire.     

```agda
is-distance-between-multiples-div-mod-ℕ :
  (x y z : ℕ) →
  div-ℤ-Mod x (mod-ℕ x y) (mod-ℕ x z) → is-distance-between-multiples-ℕ x y z
is-distance-between-multiples-div-mod-ℕ zero-ℕ y z (u , p)
  with (decide-is-nonnegative-ℤ {u}) in eq
... | inl nonneg = (zero-ℕ , abs-ℤ u , 
  is-injective-int-ℕ (inv (mul-int-ℕ (abs-ℤ u) y) 
    ∙ (ap (λ p → mul-ℤ p (int-ℕ y)) (int-abs-is-nonnegative-ℤ u nonneg) ∙ p)))
... | inr neg = (zero-ℕ , zero-ℕ , path)
  where 
  path : zero-ℕ ＝ z 
  path = is-injective-int-ℕ (inv 
    (is-zero-is-nonnegative-neg-is-nonnegative-ℤ (int-ℕ z) (is-nonnegative-int-ℕ z) 
      (tr is-nonnegative-ℤ 
        (left-negative-law-mul-ℤ u (int-ℕ y) ∙ ap (neg-ℤ) p) 
        (is-nonnegative-mul-ℤ neg (is-nonnegative-int-ℕ y))))) 
  
is-distance-between-multiples-div-mod-ℕ (succ-ℕ x) y z (u , p)
  with (decide-is-nonnegative-ℤ 
        {add-ℤ (mul-ℤ (int-ℤ-Mod (succ-ℕ x) u) (int-ℕ y)) (neg-ℤ (int-ℕ z))})
... | inl uy-z = (abs-ℤ a , nat-Fin (succ-ℕ x) u , lem3)
  where
  lem : cong-ℤ (int-ℕ (succ-ℕ x)) 
    (mul-ℤ (int-ℤ-Mod (succ-ℕ x) u) (int-ℕ y)) (int-ℕ z)
  lem = cong-eq-mod-ℤ (succ-ℕ x) 
    (mul-ℤ (int-ℤ-Mod (succ-ℕ x) u) (int-ℕ y)) (int-ℕ z) 
    ( preserves-mul-mod-ℤ (succ-ℕ x) (int-ℤ-Mod (succ-ℕ x) u) (int-ℕ y) 
    ∙ ( ap (λ p → mul-ℤ-Mod (succ-ℕ x) p (mod-ℤ (succ-ℕ x) (int-ℕ y))) 
      (issec-int-ℤ-Mod (succ-ℕ x) u) 
    ∙ ( ap (λ p → mul-ℤ-Mod (succ-ℕ x) u p) (mod-int-ℕ (succ-ℕ x) y) 
    ∙ ( p 
    ∙ ( inv (mod-int-ℕ (succ-ℕ x) z))))))

  a : ℤ
  a = pr1 lem

  path : mul-ℤ a (int-ℕ (succ-ℕ x)) ＝ add-ℤ (mul-ℤ (int-ℤ-Mod (succ-ℕ x) u) 
    (int-ℕ y)) (neg-ℤ (int-ℕ z)) 
  path = pr2 lem

  lem2 : add-ℤ (mul-ℤ (int-ℤ-Mod (succ-ℕ x) u) (int-ℕ y)) 
    (neg-ℤ (mul-ℤ a (int-ℕ (succ-ℕ x)))) ＝ int-ℕ z 
  lem2 = commutative-add-ℤ (mul-ℤ (int-ℤ-Mod (succ-ℕ x) u) (int-ℕ y)) 
    (neg-ℤ (mul-ℤ a (int-ℕ (succ-ℕ x)))) 
    ∙ ( ap (λ p → add-ℤ p (mul-ℤ (int-ℤ-Mod (succ-ℕ x) u) (int-ℕ y))) 
      (inv (left-negative-law-mul-ℤ a (int-ℕ (succ-ℕ x)))) 
    ∙ ( ap (λ p → add-ℤ (mul-ℤ (neg-ℤ a) (int-ℕ (succ-ℕ x))) p) 
      (inv (issec-add-neg-ℤ' (int-ℕ z) 
      (mul-ℤ (int-ℤ-Mod (succ-ℕ x) u) (int-ℕ y)))) 
    ∙ ( inv (associative-add-ℤ (mul-ℤ (neg-ℤ a) (int-ℕ (succ-ℕ x))) 
      (add-ℤ (mul-ℤ (int-ℤ-Mod (succ-ℕ x) u) (int-ℕ y)) (neg-ℤ (int-ℕ z))) 
      (int-ℕ z))
    ∙ ( ap (λ p → add-ℤ (add-ℤ (mul-ℤ (neg-ℤ a) (int-ℕ (succ-ℕ x))) p)
             (int-ℕ z)) 
      (inv path) 
    ∙ ( ap (λ p → add-ℤ (add-ℤ p (mul-ℤ a (int-ℕ (succ-ℕ x)))) (int-ℕ z)) 
      (left-negative-law-mul-ℤ a (int-ℕ (succ-ℕ x))) 
    ∙ ( ap (λ p → add-ℤ p (int-ℕ z)) 
      (left-inverse-law-add-ℤ (mul-ℤ a (int-ℕ (succ-ℕ x)))) 
    ∙ ( left-unit-law-add-ℤ (int-ℕ z)))))))) 

  a-factor-int-ℕ : int-ℕ (abs-ℤ a) ＝ a
  a-factor-int-ℕ = int-abs-is-nonnegative-ℤ a 
    (is-nonnegative-left-factor-mul-ℤ (tr is-nonnegative-ℤ (inv path) uy-z) 
    (is-nonnegative-int-ℕ (succ-ℕ x))) 

  lem3 : dist-ℕ (mul-ℕ (abs-ℤ a) (succ-ℕ x)) 
    (mul-ℕ (nat-Fin (succ-ℕ x) u) y)  ＝ z 
  lem3 = symmetric-dist-ℕ (mul-ℕ (abs-ℤ a) (succ-ℕ x)) 
    (mul-ℕ (nat-Fin (succ-ℕ x) u) y) 
    ∙ ( inv (dist-int-ℕ (mul-ℕ (nat-Fin (succ-ℕ x) u) y)
      (mul-ℕ (abs-ℤ a)  (succ-ℕ x))) 
    ∙ ( ap (λ p → dist-ℤ (int-ℕ (mul-ℕ (nat-Fin (succ-ℕ x) u) y)) p) 
      (inv (mul-int-ℕ (abs-ℤ a) (succ-ℕ x)))  
    ∙ ( ap (λ p → dist-ℤ p (mul-ℤ (int-ℕ (abs-ℤ a)) (int-ℕ (succ-ℕ x)))) 
      (inv (mul-int-ℕ (nat-Fin (succ-ℕ x) u) y)) 
    ∙ ( ap (λ p → dist-ℤ (mul-ℤ (int-ℤ-Mod (succ-ℕ x) u) (int-ℕ y)) 
             (mul-ℤ p  (int-ℕ (succ-ℕ x))))
      a-factor-int-ℕ  
    ∙ ( ap (abs-ℤ) lem2 ∙ abs-int-ℕ z)))))

... | inr z-uy = (add-ℕ (abs-ℤ a) y , 
  abs-ℤ (add-ℤ (int-ℕ (succ-ℕ x)) (neg-ℤ (int-ℤ-Mod (succ-ℕ x) u))) , lem3)
  where
  lem : cong-ℤ (int-ℕ (succ-ℕ x)) (int-ℕ z) 
    (mul-ℤ (int-ℤ-Mod (succ-ℕ x) u) (int-ℕ y))
  lem = symmetric-cong-ℤ (int-ℕ (succ-ℕ x)) 
    ( mul-ℤ (int-ℤ-Mod (succ-ℕ x) u) (int-ℕ y)) (int-ℕ z) 
    ( cong-eq-mod-ℤ (succ-ℕ x) (mul-ℤ (int-ℤ-Mod (succ-ℕ x) u) (int-ℕ y)) 
      (int-ℕ z) 
    ( preserves-mul-mod-ℤ (succ-ℕ x) (int-ℤ-Mod (succ-ℕ x) u) (int-ℕ y) 
    ∙ ( ap (λ p → mul-ℤ-Mod (succ-ℕ x) p (mod-ℤ (succ-ℕ x) (int-ℕ y))) 
      (issec-int-ℤ-Mod (succ-ℕ x) u) 
    ∙ ( ap (λ p → mul-ℤ-Mod (succ-ℕ x) u p) (mod-int-ℕ (succ-ℕ x) y) 
    ∙ ( p 
    ∙ ( inv (mod-int-ℕ (succ-ℕ x) z)))))))

  a : ℤ
  a = pr1 lem

  path : mul-ℤ a (int-ℕ (succ-ℕ x)) ＝ add-ℤ (int-ℕ z) 
    (neg-ℤ (mul-ℤ (int-ℤ-Mod (succ-ℕ x) u) (int-ℕ y)))   
  path = pr2 lem

  lem2 : add-ℤ (mul-ℤ (add-ℤ a (int-ℕ y)) (int-ℕ (succ-ℕ x))) 
    (neg-ℤ (mul-ℤ (add-ℤ (int-ℕ (succ-ℕ x)) (neg-ℤ (int-ℤ-Mod (succ-ℕ x) u)))
      (int-ℕ y))) ＝ int-ℕ z
  lem2 = ap (λ p → add-ℤ (mul-ℤ (add-ℤ a (int-ℕ y)) (int-ℕ (succ-ℕ x))) p) 
    (inv (left-negative-law-mul-ℤ (add-ℤ (int-ℕ (succ-ℕ x)) 
      (neg-ℤ (int-ℤ-Mod (succ-ℕ x) u))) (int-ℕ y)))
    ∙ ( ap (λ p → add-ℤ (mul-ℤ (add-ℤ a (int-ℕ y)) (int-ℕ (succ-ℕ x))) 
             (mul-ℤ p (int-ℕ y))) 
      (ap (neg-ℤ) (commutative-add-ℤ (int-ℕ (succ-ℕ x)) 
        (neg-ℤ (int-ℤ-Mod (succ-ℕ x) u))) 
    ∙ ( ap (λ p → neg-ℤ (add-ℤ (neg-ℤ (int-ℤ-Mod (succ-ℕ x) u)) p)) 
      (inv (neg-neg-ℤ (int-ℕ (succ-ℕ x)))) 
    ∙ ( ap (neg-ℤ) (inv (distributive-neg-add-ℤ (int-ℤ-Mod (succ-ℕ x) u) 
      (neg-ℤ (int-ℕ (succ-ℕ x)))))
    ∙ ( neg-neg-ℤ (add-ℤ (int-ℤ-Mod (succ-ℕ x) u) (neg-ℤ (int-ℕ (succ-ℕ x)))))))) 
    ∙ ( ap (λ p → add-ℤ (mul-ℤ (add-ℤ a (int-ℕ y)) (int-ℕ (succ-ℕ x))) p) 
      (right-distributive-mul-add-ℤ (int-ℤ-Mod (succ-ℕ x) u) 
        (neg-ℤ (int-ℕ (succ-ℕ x))) (int-ℕ y) ) 
    ∙ ( ap (λ p → add-ℤ (mul-ℤ (add-ℤ a (int-ℕ y)) (int-ℕ (succ-ℕ x))) 
             (add-ℤ (mul-ℤ (int-ℤ-Mod (succ-ℕ x) u) (int-ℕ y)) p)) 
      (left-negative-law-mul-ℤ (int-ℕ (succ-ℕ x)) (int-ℕ y)) 
    ∙ ( ap (λ p → add-ℤ p (add-ℤ (mul-ℤ (int-ℤ-Mod (succ-ℕ x) u) (int-ℕ y)) 
             (neg-ℤ (mul-ℤ (int-ℕ (succ-ℕ x)) (int-ℕ y))))) 
      (right-distributive-mul-add-ℤ a (int-ℕ y) (int-ℕ (succ-ℕ x))) 
    ∙ ( ap (λ p → add-ℤ (add-ℤ (mul-ℤ a (int-ℕ (succ-ℕ x))) p) 
             (add-ℤ (mul-ℤ (int-ℤ-Mod (succ-ℕ x) u) (int-ℕ y)) 
             (neg-ℤ (mul-ℤ (int-ℕ (succ-ℕ x)) (int-ℕ y)))))  
      (commutative-mul-ℤ  (int-ℕ y) (int-ℕ (succ-ℕ x))) 
    ∙ ( associative-add-ℤ (mul-ℤ a (int-ℕ (succ-ℕ x))) 
      (mul-ℤ (int-ℕ (succ-ℕ x)) (int-ℕ y)) 
      (add-ℤ (mul-ℤ (int-ℤ-Mod (succ-ℕ x) u) (int-ℕ y)) 
        (neg-ℤ (mul-ℤ (int-ℕ (succ-ℕ x)) (int-ℕ y))))
    ∙ ( ap (λ p → add-ℤ (mul-ℤ a (int-ℕ (succ-ℕ x))) p) 
      (commutative-add-ℤ (mul-ℤ (int-ℕ (succ-ℕ x)) (int-ℕ y)) 
        (add-ℤ (mul-ℤ (int-ℤ-Mod (succ-ℕ x) u) (int-ℕ y)) 
          (neg-ℤ (mul-ℤ (int-ℕ (succ-ℕ x)) (int-ℕ y)))))  
    ∙ ( ap (λ p → add-ℤ (mul-ℤ a (int-ℕ (succ-ℕ x))) p) 
      (associative-add-ℤ (mul-ℤ (int-ℤ-Mod (succ-ℕ x) u) (int-ℕ y)) 
        (neg-ℤ (mul-ℤ (int-ℕ (succ-ℕ x)) (int-ℕ y))) 
        (mul-ℤ (int-ℕ (succ-ℕ x)) (int-ℕ y)))
    ∙ ( inv (associative-add-ℤ (mul-ℤ a (int-ℕ (succ-ℕ x))) 
        (mul-ℤ (int-ℤ-Mod (succ-ℕ x) u) (int-ℕ y)) 
        (add-ℤ (neg-ℤ (mul-ℤ (int-ℕ (succ-ℕ x)) (int-ℕ y))) 
          (mul-ℤ (int-ℕ (succ-ℕ x)) (int-ℕ y)))) 
    ∙ ( ap (λ p → add-ℤ (add-ℤ (mul-ℤ a (int-ℕ (succ-ℕ x))) 
             (mul-ℤ (int-ℤ-Mod (succ-ℕ x) u) (int-ℕ y))) p) 
      (left-inverse-law-add-ℤ (mul-ℤ (int-ℕ (succ-ℕ x)) (int-ℕ y)))
    ∙ ( right-unit-law-add-ℤ (add-ℤ (mul-ℤ a (int-ℕ (succ-ℕ x))) 
      (mul-ℤ (int-ℤ-Mod (succ-ℕ x) u) (int-ℕ y))) 
    ∙ ( ap (λ p → add-ℤ p (mul-ℤ (int-ℤ-Mod (succ-ℕ x) u) (int-ℕ y))) path 
    ∙ issec-add-neg-ℤ' (mul-ℤ (int-ℤ-Mod (succ-ℕ x) u) (int-ℕ y)) 
      (int-ℕ z)))))))))))))

  a-factor-int-ℕ : int-ℕ (abs-ℤ a) ＝ a
  a-factor-int-ℕ = int-abs-is-nonnegative-ℤ a (is-nonnegative-left-factor-mul-ℤ 
    (tr is-nonnegative-ℤ 
    (distributive-neg-add-ℤ (mul-ℤ (int-ℤ-Mod (succ-ℕ x) u) (int-ℕ y)) 
      (neg-ℤ (int-ℕ z)) 
      ∙ ( ap (λ p → add-ℤ (neg-ℤ (mul-ℤ (int-ℤ-Mod (succ-ℕ x) u) (int-ℕ y))) p)
        (neg-neg-ℤ (int-ℕ z))  
      ∙ ( commutative-add-ℤ (neg-ℤ (mul-ℤ (int-ℤ-Mod (succ-ℕ x) u) (int-ℕ y)))
        (int-ℕ z)  
      ∙ inv path))) 
    (z-uy)) (is-nonnegative-int-ℕ (succ-ℕ x))) 

  x-u-factor-int-ℕ : 
    int-ℕ (abs-ℤ (add-ℤ (int-ℕ (succ-ℕ x)) (neg-ℤ (int-ℤ-Mod (succ-ℕ x) u)))) 
    ＝ (add-ℤ (int-ℕ (succ-ℕ x)) (neg-ℤ (int-ℤ-Mod (succ-ℕ x) u)))   
  x-u-factor-int-ℕ = int-abs-is-nonnegative-ℤ (add-ℤ (int-ℕ (succ-ℕ x)) 
    (neg-ℤ (int-ℤ-Mod (succ-ℕ x) u))) (int-ℤ-Mod-bounded x u)

  lem3 : dist-ℕ (mul-ℕ (add-ℕ (abs-ℤ a) y) (succ-ℕ x)) 
    (mul-ℕ (abs-ℤ (add-ℤ (int-ℕ (succ-ℕ x)) 
      (neg-ℤ (int-ℤ-Mod (succ-ℕ x) u)))) y) ＝ z
  lem3 = inv (dist-int-ℕ (mul-ℕ (add-ℕ (abs-ℤ a) y) (succ-ℕ x)) 
    (mul-ℕ (abs-ℤ (add-ℤ (int-ℕ (succ-ℕ x)) 
      (neg-ℤ (int-ℤ-Mod (succ-ℕ x) u)))) y)) 
    ∙ ( ap (λ p → dist-ℤ p (int-ℕ (mul-ℕ (abs-ℤ (add-ℤ (int-ℕ (succ-ℕ x)) 
             (neg-ℤ (int-ℤ-Mod (succ-ℕ x) u)))) y))) 
      (inv (mul-int-ℕ (add-ℕ (abs-ℤ a) y) (succ-ℕ x))) 
    ∙ ( ap (λ p → dist-ℤ (mul-ℤ p (int-ℕ (succ-ℕ x))) 
             (int-ℕ (mul-ℕ (abs-ℤ (add-ℤ (int-ℕ (succ-ℕ x)) 
               (neg-ℤ (int-ℤ-Mod (succ-ℕ x) u)))) y))) 
      (inv (add-int-ℕ (abs-ℤ a) y)) 
    ∙ ( ap (λ p → dist-ℤ (mul-ℤ (add-ℤ (int-ℕ (abs-ℤ a)) (int-ℕ y)) 
             (int-ℕ (succ-ℕ x))) p) 
      (inv (mul-int-ℕ (abs-ℤ (add-ℤ (int-ℕ (succ-ℕ x)) 
        (neg-ℤ (int-ℤ-Mod (succ-ℕ x) u)))) y)) 
    ∙ ( ap (λ p → dist-ℤ (mul-ℤ (add-ℤ (int-ℕ (abs-ℤ a)) (int-ℕ y)) 
             (int-ℕ (succ-ℕ x))) (mul-ℤ p (int-ℕ y))) 
      (x-u-factor-int-ℕ)
    ∙ ( ap (λ p → dist-ℤ (mul-ℤ (add-ℤ p (int-ℕ y)) (int-ℕ (succ-ℕ x))) 
             (mul-ℤ (add-ℤ (int-ℕ (succ-ℕ x)) (neg-ℤ (int-ℤ-Mod (succ-ℕ x) u)))
                (int-ℕ y)) ) a-factor-int-ℕ 
    ∙ ( ap (abs-ℤ) lem2 ∙ abs-int-ℕ z))))))

```

### The type `is-distance-between-multiples-ℕ x y z` is decidable

```agda
is-decidable-is-distance-between-multiples-ℕ :
  (x y z : ℕ) → is-decidable (is-distance-between-multiples-ℕ x y z)
is-decidable-is-distance-between-multiples-ℕ x y z
  with (is-decidable-div-ℤ-Mod x (mod-ℕ x y) (mod-ℕ x z))
... | inl div-Mod = inl (is-distance-between-multiples-div-mod-ℕ x y z div-Mod)
... | inr neg-div-Mod = inr (λ dist → neg-div-Mod (div-mod-is-distance-between-multiples-ℕ x y z dist)) 
```

## Theorem

Since `is-distance-between-multiples-ℕ x y z` is decidable, we can prove Bezout's lemma by the well-ordering principle. First, take the least positive distance `d` between multiples of `x` and `y`. 

```agda
pos-distance-between-multiples : (x y z : ℕ) → UU lzero
pos-distance-between-multiples x y z = is-nonzero-ℕ (add-ℕ x y) → 
  (is-nonzero-ℕ z) × (is-distance-between-multiples-ℕ x y z)   

is-inhabited-pos-distance-between-multiples : (x y : ℕ) → 
  Σ ℕ (pos-distance-between-multiples x y)
is-inhabited-pos-distance-between-multiples zero-ℕ zero-ℕ = 
  pair zero-ℕ (λ H → ex-falso (H refl))
is-inhabited-pos-distance-between-multiples zero-ℕ (succ-ℕ y) = 
  pair (succ-ℕ y) (λ H → pair' (is-nonzero-succ-ℕ y) 
    (pair zero-ℕ (pair 1 (ap succ-ℕ (left-unit-law-add-ℕ y)))))
is-inhabited-pos-distance-between-multiples (succ-ℕ x) y = pair (succ-ℕ x)
  (λ H → pair' (is-nonzero-succ-ℕ x) 
    (pair 1 (pair zero-ℕ (ap succ-ℕ (left-unit-law-add-ℕ x)))))

minimal-pos-distance-between-multiples : (x y : ℕ) → 
  minimal-element-ℕ (pos-distance-between-multiples x y)
minimal-pos-distance-between-multiples x y = well-ordering-principle-ℕ 
  (pos-distance-between-multiples x y)
  (λ z → is-decidable-function-type 
    (is-decidable-neg (is-decidable-is-zero-ℕ (add-ℕ x y))) 
    (is-decidable-prod (is-decidable-neg (is-decidable-is-zero-ℕ z)) 
      (is-decidable-is-distance-between-multiples-ℕ x y z))) 
  (is-inhabited-pos-distance-between-multiples x y)

minimal-positive-distance : (x y : ℕ) → ℕ
minimal-positive-distance x y = pr1 (minimal-pos-distance-between-multiples x y)
```

Then `d` divides both `x` and `y`. Since `gcd x y` divides any number of the form `dist-ℕ (kx,ly)`, it follows that `gcd x y | d`, and hence that `gcd x y ＝ d`.

```agda
minimal-positive-distance-is-distance : (x y : ℕ) → is-nonzero-ℕ (add-ℕ x y) → (is-distance-between-multiples-ℕ x y (minimal-positive-distance x y))
minimal-positive-distance-is-distance x y nonzero = pr2 ((pr1 (pr2 (minimal-pos-distance-between-multiples x y))) nonzero)

minimal-positive-distance-is-minimal : (x y : ℕ) → is-lower-bound-ℕ (pos-distance-between-multiples x y) (minimal-positive-distance x y) 
minimal-positive-distance-is-minimal x y = pr2 (pr2 (minimal-pos-distance-between-multiples x y))

minimal-positive-distance-nonzero : (x y : ℕ) → (is-nonzero-ℕ (add-ℕ x y)) → (is-nonzero-ℕ (minimal-positive-distance x y))
minimal-positive-distance-nonzero x y nonzero = pr1 ((pr1 (pr2 (minimal-pos-distance-between-multiples x y))) nonzero) 

minimal-positive-distance-leq-sym : (x y : ℕ) → leq-ℕ (minimal-positive-distance x y) (minimal-positive-distance y x)
minimal-positive-distance-leq-sym x y = minimal-positive-distance-is-minimal x y (minimal-positive-distance y x) 
  (λ H → pair' 
    (minimal-positive-distance-nonzero y x (λ K → H (commutative-add-ℕ x y ∙ K))) 
     (is-distance-between-multiples-sym-ℕ y x (minimal-positive-distance y x) (minimal-positive-distance-is-distance y x (λ K → H (commutative-add-ℕ x y ∙ K))))) 

minimal-positive-distance-sym : (x y : ℕ) → minimal-positive-distance x y ＝ minimal-positive-distance y x 
minimal-positive-distance-sym x y = antisymmetric-leq-ℕ
  (minimal-positive-distance x y)
  (minimal-positive-distance y x)
  (minimal-positive-distance-leq-sym x y)
  (minimal-positive-distance-leq-sym y x)

minimal-positive-distance-x-coeff : (x y : ℕ) → (is-nonzero-ℕ (add-ℕ x y)) → ℕ
minimal-positive-distance-x-coeff x y H = pr1 (minimal-positive-distance-is-distance x y H)

minimal-positive-distance-succ-x-coeff : (x y : ℕ) → ℕ
minimal-positive-distance-succ-x-coeff x y = minimal-positive-distance-x-coeff (succ-ℕ x) y (tr is-nonzero-ℕ (inv (left-successor-law-add-ℕ x y)) (is-nonzero-succ-ℕ (add-ℕ x y)))  

minimal-positive-distance-y-coeff : (x y : ℕ) → (is-nonzero-ℕ (add-ℕ x y)) → ℕ 
minimal-positive-distance-y-coeff x y H = pr1 (pr2 (minimal-positive-distance-is-distance x y H))

minimal-positive-distance-succ-y-coeff : (x y : ℕ) → ℕ
minimal-positive-distance-succ-y-coeff x y = minimal-positive-distance-y-coeff (succ-ℕ x) y (tr is-nonzero-ℕ (inv (left-successor-law-add-ℕ x y)) (is-nonzero-succ-ℕ (add-ℕ x y)))

minimal-positive-distance-eqn : (x y : ℕ) → (H : is-nonzero-ℕ (add-ℕ x y)) → dist-ℕ (mul-ℕ (minimal-positive-distance-x-coeff x y H) x) (mul-ℕ (minimal-positive-distance-y-coeff x y H) y) ＝ minimal-positive-distance x y
minimal-positive-distance-eqn x y H = pr2 (pr2 (minimal-positive-distance-is-distance x y H))

minimal-positive-distance-succ-eqn : (x y : ℕ) → dist-ℕ (mul-ℕ (minimal-positive-distance-succ-x-coeff x y) (succ-ℕ x)) (mul-ℕ (minimal-positive-distance-succ-y-coeff x y) y) ＝ minimal-positive-distance (succ-ℕ x) y 
minimal-positive-distance-succ-eqn x y = minimal-positive-distance-eqn (succ-ℕ x) y (tr is-nonzero-ℕ (inv (left-successor-law-add-ℕ x y)) (is-nonzero-succ-ℕ (add-ℕ x y)))

minimal-positive-distance-div-succ-x-eqn : (x y : ℕ) → add-ℤ  
    (mul-ℤ (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))) (int-ℕ (minimal-positive-distance (succ-ℕ x) y))) 
    (int-ℕ (remainder-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))) ＝ int-ℕ (succ-ℕ x)
minimal-positive-distance-div-succ-x-eqn x y = 
    equational-reasoning
      add-ℤ 
        (mul-ℤ (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))) (int-ℕ (minimal-positive-distance (succ-ℕ x) y))) 
        (int-ℕ (remainder-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
      ＝ add-ℤ
        (int-ℕ (mul-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)) (minimal-positive-distance (succ-ℕ x) y)))
        (int-ℕ (remainder-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))) 
          by (ap (λ H → add-ℤ H (int-ℕ (remainder-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))) (mul-int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)) (minimal-positive-distance (succ-ℕ x) y)))
       ＝ int-ℕ (add-ℕ
        (mul-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)) (minimal-positive-distance (succ-ℕ x) y))
        (remainder-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)) ) 
          by (add-int-ℕ (mul-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)) (minimal-positive-distance (succ-ℕ x) y)) (remainder-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
       ＝ int-ℕ (succ-ℕ x) 
          by ap (int-ℕ) (eq-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)) 

remainder-min-dist-succ-x-le-min-dist : (x y : ℕ) → le-ℕ (remainder-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)) (minimal-positive-distance (succ-ℕ x) y)
remainder-min-dist-succ-x-le-min-dist x y = strict-upper-bound-remainder-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x) (minimal-positive-distance-nonzero (succ-ℕ x) y (tr (is-nonzero-ℕ) (inv (left-successor-law-add-ℕ x y)) (is-nonzero-succ-ℕ (add-ℕ x y)))) 

remainder-min-dist-succ-x-is-distance : (x y : ℕ) → 
  (is-distance-between-multiples-ℕ (succ-ℕ x) y 
    (remainder-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
remainder-min-dist-succ-x-is-distance x y with decide-leq-ℕ (mul-ℕ (minimal-positive-distance-succ-x-coeff x y) (succ-ℕ x)) (mul-ℕ (minimal-positive-distance-succ-y-coeff x y) y)
... | inl sxty = pair (add-ℕ 
        (mul-ℕ 
          (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)) 
          (minimal-positive-distance-succ-x-coeff x y)) 1)
         (pair (mul-ℕ  
          (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)) 
          (minimal-positive-distance-succ-y-coeff x y)) (inv dist-eqn))
  where
  add-dist-eqn : int-ℕ (minimal-positive-distance (succ-ℕ x) y) ＝ 
    add-ℤ
      (mul-ℤ (int-ℕ (minimal-positive-distance-succ-y-coeff x y)) (int-ℕ y)) 
      ((mul-ℤ (neg-ℤ (int-ℕ (minimal-positive-distance-succ-x-coeff x y))) (int-ℕ (succ-ℕ x))))
  add-dist-eqn = (((inv (isretr-add-neg-ℤ' (int-ℕ (mul-ℕ (minimal-positive-distance-succ-x-coeff x y) (succ-ℕ x))) (int-ℕ (minimal-positive-distance (succ-ℕ x) y)) )
    ∙ (ap (λ H → add-ℤ H (neg-ℤ (int-ℕ (mul-ℕ (minimal-positive-distance-succ-x-coeff x y) (succ-ℕ x))))) 
      (add-int-ℕ (minimal-positive-distance (succ-ℕ x) y) (mul-ℕ (minimal-positive-distance-succ-x-coeff x y) (succ-ℕ x))
      ∙ ap int-ℕ (rewrite-left-dist-add-ℕ (minimal-positive-distance (succ-ℕ x) y) (mul-ℕ (minimal-positive-distance-succ-x-coeff x y) (succ-ℕ x)) (mul-ℕ (minimal-positive-distance-succ-y-coeff x y) y) sxty (inv (minimal-positive-distance-succ-eqn x y))))))
      ∙ ap (λ H → add-ℤ H (neg-ℤ (int-ℕ (mul-ℕ (minimal-positive-distance-succ-x-coeff x y) (succ-ℕ x))))) (inv (mul-int-ℕ (minimal-positive-distance-succ-y-coeff x y) y)))
      ∙ ap (λ H → add-ℤ (mul-ℤ (int-ℕ (minimal-positive-distance-succ-y-coeff x y)) (int-ℕ y)) (neg-ℤ H)) (inv (mul-int-ℕ (minimal-positive-distance-succ-x-coeff x y) (succ-ℕ x))))
      ∙ ap (λ H → add-ℤ (mul-ℤ (int-ℕ (minimal-positive-distance-succ-y-coeff x y)) (int-ℕ y)) H) (inv (left-negative-law-mul-ℤ (int-ℕ (minimal-positive-distance-succ-x-coeff x y)) (int-ℕ (succ-ℕ x))))

  isolate-rem-eqn : int-ℕ (remainder-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)) ＝ 
    add-ℤ 
      (neg-ℤ (mul-ℤ 
        (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))) 
        (add-ℤ
           (mul-ℤ (int-ℕ (minimal-positive-distance-succ-y-coeff x y)) (int-ℕ y)) 
           (mul-ℤ (neg-ℤ (int-ℕ (minimal-positive-distance-succ-x-coeff x y))) (int-ℕ (succ-ℕ x))) )))
      (int-ℕ (succ-ℕ x))
  isolate-rem-eqn = 
    equational-reasoning
      (int-ℕ (remainder-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
      ＝ add-ℤ
      (neg-ℤ (mul-ℤ 
        (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))) 
        (add-ℤ
           (mul-ℤ (int-ℕ (minimal-positive-distance-succ-y-coeff x y)) (int-ℕ y)) 
           (mul-ℤ (neg-ℤ (int-ℕ (minimal-positive-distance-succ-x-coeff x y))) (int-ℕ (succ-ℕ x))) ))) 
      (add-ℤ  
        (mul-ℤ 
          (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))) 
          (add-ℤ
            (mul-ℤ (int-ℕ (minimal-positive-distance-succ-y-coeff x y)) (int-ℕ y)) 
            (mul-ℤ (neg-ℤ (int-ℕ (minimal-positive-distance-succ-x-coeff x y))) (int-ℕ (succ-ℕ x))) )) 
       (int-ℕ (remainder-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))) 
         by (inv (isretr-add-neg-ℤ
           (mul-ℤ 
             (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))) 
             (add-ℤ
               (mul-ℤ (int-ℕ (minimal-positive-distance-succ-y-coeff x y)) (int-ℕ y)) 
               (mul-ℤ (neg-ℤ (int-ℕ (minimal-positive-distance-succ-x-coeff x y))) (int-ℕ (succ-ℕ x))))) (int-ℕ (remainder-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))))
        ＝ add-ℤ
        (neg-ℤ (mul-ℤ 
          (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))) 
          (add-ℤ
           (mul-ℤ (int-ℕ (minimal-positive-distance-succ-y-coeff x y)) (int-ℕ y)) 
           (mul-ℤ (neg-ℤ (int-ℕ (minimal-positive-distance-succ-x-coeff x y))) (int-ℕ (succ-ℕ x))) ))) 
        (add-ℤ  
          (mul-ℤ 
            (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))) 
            (int-ℕ (minimal-positive-distance (succ-ℕ x) y))  ) 
          (int-ℕ (remainder-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))) 
          by (ap (λ H → add-ℤ
          (neg-ℤ (mul-ℤ 
            (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))) 
            (add-ℤ
              (mul-ℤ (int-ℕ (minimal-positive-distance-succ-y-coeff x y)) (int-ℕ y)) 
              (mul-ℤ (neg-ℤ (int-ℕ (minimal-positive-distance-succ-x-coeff x y))) (int-ℕ (succ-ℕ x))) ))) 
          (add-ℤ  
            (mul-ℤ 
              (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))) 
              H) 
            (int-ℕ (remainder-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))))) 
            (inv add-dist-eqn))
        ＝ add-ℤ 
        (neg-ℤ (mul-ℤ 
          (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))) 
          (add-ℤ
             (mul-ℤ (int-ℕ (minimal-positive-distance-succ-y-coeff x y)) (int-ℕ y)) 
             (mul-ℤ (neg-ℤ (int-ℕ (minimal-positive-distance-succ-x-coeff x y))) (int-ℕ (succ-ℕ x))) )))
        (int-ℕ (succ-ℕ x))
          by (ap (λ H → add-ℤ 
            (neg-ℤ (mul-ℤ 
              (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))) 
            (add-ℤ
               (mul-ℤ (int-ℕ (minimal-positive-distance-succ-y-coeff x y)) (int-ℕ y)) 
               (mul-ℤ (neg-ℤ (int-ℕ (minimal-positive-distance-succ-x-coeff x y))) (int-ℕ (succ-ℕ x))) ))) H) (minimal-positive-distance-div-succ-x-eqn x y)) 


  rearrange-arith-eqn : add-ℤ 
    (neg-ℤ (mul-ℤ 
      (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))) 
      (add-ℤ
        (mul-ℤ (int-ℕ (minimal-positive-distance-succ-y-coeff x y)) (int-ℕ y)) 
        (mul-ℤ (neg-ℤ (int-ℕ (minimal-positive-distance-succ-x-coeff x y))) (int-ℕ (succ-ℕ x))) )))
      (int-ℕ (succ-ℕ x)) ＝ 
    add-ℤ
      (mul-ℤ (add-ℤ 
        (mul-ℤ 
          (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))) 
          (int-ℕ (minimal-positive-distance-succ-x-coeff x y))) 
         one-ℤ) 
        (int-ℕ (succ-ℕ x)))
      (neg-ℤ (mul-ℤ
        (mul-ℤ 
          (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))) 
          (int-ℕ (minimal-positive-distance-succ-y-coeff x y))) 
        (int-ℕ y)))
  rearrange-arith-eqn = 
    equational-reasoning
      add-ℤ 
        (neg-ℤ (mul-ℤ 
          (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))) 
          (add-ℤ
            (mul-ℤ (int-ℕ (minimal-positive-distance-succ-y-coeff x y)) (int-ℕ y)) 
            (mul-ℤ (neg-ℤ (int-ℕ (minimal-positive-distance-succ-x-coeff x y))) (int-ℕ (succ-ℕ x))) )))
      (int-ℕ (succ-ℕ x))
      ＝ add-ℤ 
           (neg-ℤ (add-ℤ 
             (mul-ℤ 
               (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
               (mul-ℤ (int-ℕ (minimal-positive-distance-succ-y-coeff x y)) (int-ℕ y)))
             (mul-ℤ 
               (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
               (mul-ℤ (neg-ℤ (int-ℕ (minimal-positive-distance-succ-x-coeff x y))) (int-ℕ (succ-ℕ x))) )))
            (int-ℕ (succ-ℕ x))
           by (ap (λ H → add-ℤ (neg-ℤ H) (int-ℕ (succ-ℕ x)))
             (left-distributive-mul-add-ℤ (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
               (mul-ℤ (int-ℕ (minimal-positive-distance-succ-y-coeff x y)) (int-ℕ y)) 
               (mul-ℤ (neg-ℤ (int-ℕ (minimal-positive-distance-succ-x-coeff x y))) (int-ℕ (succ-ℕ x)))))
       ＝ add-ℤ 
            (neg-ℤ (add-ℤ 
              (mul-ℤ 
                (mul-ℤ 
                  (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))) 
                  (int-ℕ (minimal-positive-distance-succ-y-coeff x y)))
                (int-ℕ y))
             (mul-ℤ 
               (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
               (mul-ℤ (neg-ℤ (int-ℕ (minimal-positive-distance-succ-x-coeff x y))) (int-ℕ (succ-ℕ x))) )))
             (int-ℕ (succ-ℕ x))
            by (ap (λ H → add-ℤ (neg-ℤ (add-ℤ H 
              (mul-ℤ 
                (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
                (mul-ℤ (neg-ℤ (int-ℕ (minimal-positive-distance-succ-x-coeff x y))) (int-ℕ (succ-ℕ x))) )))
              (int-ℕ (succ-ℕ x)))
              (inv (associative-mul-ℤ 
                  (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
                  (int-ℕ (minimal-positive-distance-succ-y-coeff x y))
                  (int-ℕ y))))
          ＝ add-ℤ 
            (neg-ℤ (add-ℤ 
              (mul-ℤ 
                (mul-ℤ 
                  (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))) 
                  (int-ℕ (minimal-positive-distance-succ-y-coeff x y)))
                (int-ℕ y))
              (neg-ℤ (mul-ℤ 
                ((mul-ℤ 
                  (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
                  ((int-ℕ (minimal-positive-distance-succ-x-coeff x y))))) 
              (int-ℕ (succ-ℕ x)))) ))
             (int-ℕ (succ-ℕ x))
            by (ap (λ H → add-ℤ (neg-ℤ (add-ℤ
              (mul-ℤ 
                (mul-ℤ 
                  (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))) 
                  (int-ℕ (minimal-positive-distance-succ-y-coeff x y)))
                (int-ℕ y))
              H ))
              (int-ℕ (succ-ℕ x)))
              ((inv (associative-mul-ℤ 
                  (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
                  (neg-ℤ (int-ℕ (minimal-positive-distance-succ-x-coeff x y)))
                  (int-ℕ (succ-ℕ x))) 
               ∙ ap (λ H → mul-ℤ H (int-ℕ (succ-ℕ x))) 
                 (right-negative-law-mul-ℤ 
                   (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))) 
                   (int-ℕ (minimal-positive-distance-succ-x-coeff x y))))
               ∙ left-negative-law-mul-ℤ 
                  (mul-ℤ 
                    (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
                    (int-ℕ (minimal-positive-distance-succ-x-coeff x y))) (int-ℕ (succ-ℕ x)) ))
          ＝ add-ℤ 
             (add-ℤ 
              (neg-ℤ (mul-ℤ 
                (mul-ℤ 
                  (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))) 
                  (int-ℕ (minimal-positive-distance-succ-y-coeff x y)))
                (int-ℕ y)))
              (neg-ℤ (neg-ℤ (mul-ℤ 
                ((mul-ℤ 
                  (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
                  ((int-ℕ (minimal-positive-distance-succ-x-coeff x y))))) 
              (int-ℕ (succ-ℕ x))))) )
             (int-ℕ (succ-ℕ x)) 
            by (ap (λ H → add-ℤ H (int-ℕ (succ-ℕ x))) 
              (distributive-neg-add-ℤ
                (mul-ℤ 
                (mul-ℤ 
                  (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))) 
                  (int-ℕ (minimal-positive-distance-succ-y-coeff x y)))
                (int-ℕ y))
                (neg-ℤ (mul-ℤ 
                ((mul-ℤ 
                  (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
                  ((int-ℕ (minimal-positive-distance-succ-x-coeff x y))))) 
              (int-ℕ (succ-ℕ x))))  ))  
           ＝ add-ℤ 
             (add-ℤ 
              (neg-ℤ (mul-ℤ 
                (mul-ℤ 
                  (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))) 
                  (int-ℕ (minimal-positive-distance-succ-y-coeff x y)))
                (int-ℕ y)))
              (mul-ℤ 
                (mul-ℤ 
                  (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
                  ((int-ℕ (minimal-positive-distance-succ-x-coeff x y)))) 
              (int-ℕ (succ-ℕ x))) )
             (int-ℕ (succ-ℕ x)) 
               by (ap (λ H → add-ℤ (add-ℤ (neg-ℤ (mul-ℤ 
                (mul-ℤ 
                  (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))) 
                  (int-ℕ (minimal-positive-distance-succ-y-coeff x y)))
                (int-ℕ y))) H) (int-ℕ (succ-ℕ x)))
                  (neg-neg-ℤ (mul-ℤ 
                (mul-ℤ 
                  (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
                  ((int-ℕ (minimal-positive-distance-succ-x-coeff x y)))) 
              (int-ℕ (succ-ℕ x)))))
            ＝ add-ℤ 
              (neg-ℤ (mul-ℤ 
                (mul-ℤ 
                  (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))) 
                  (int-ℕ (minimal-positive-distance-succ-y-coeff x y)))
                (int-ℕ y)))
              (add-ℤ (mul-ℤ 
                (mul-ℤ 
                  (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
                  ((int-ℕ (minimal-positive-distance-succ-x-coeff x y)))) 
              (int-ℕ (succ-ℕ x))) 
             (int-ℕ (succ-ℕ x))) 
            by (associative-add-ℤ
              (neg-ℤ (mul-ℤ 
                (mul-ℤ 
                  (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))) 
                  (int-ℕ (minimal-positive-distance-succ-y-coeff x y)))
                (int-ℕ y)))
              (mul-ℤ 
                (mul-ℤ 
                  (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
                  ((int-ℕ (minimal-positive-distance-succ-x-coeff x y)))) 
              (int-ℕ (succ-ℕ x)))
              (int-ℕ (succ-ℕ x)))
            ＝ add-ℤ 
              (add-ℤ (mul-ℤ 
                (mul-ℤ 
                  (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
                  ((int-ℕ (minimal-positive-distance-succ-x-coeff x y)))) 
              (int-ℕ (succ-ℕ x))) 
             (int-ℕ (succ-ℕ x)))
               (neg-ℤ (mul-ℤ 
                (mul-ℤ 
                  (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))) 
                  (int-ℕ (minimal-positive-distance-succ-y-coeff x y)))
                (int-ℕ y))) 
            by (commutative-add-ℤ 
              (neg-ℤ (mul-ℤ 
                (mul-ℤ 
                  (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))) 
                  (int-ℕ (minimal-positive-distance-succ-y-coeff x y)))
                (int-ℕ y)))
              (add-ℤ (mul-ℤ 
                (mul-ℤ 
                  (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
                  ((int-ℕ (minimal-positive-distance-succ-x-coeff x y)))) 
              (int-ℕ (succ-ℕ x))) 
             (int-ℕ (succ-ℕ x))))
             ＝ add-ℤ 
              (mul-ℤ (add-ℤ (mul-ℤ 
                  (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
                  (int-ℕ (minimal-positive-distance-succ-x-coeff x y))) 
             one-ℤ ) (int-ℕ (succ-ℕ x)) )
               (neg-ℤ (mul-ℤ 
                (mul-ℤ 
                  (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))) 
                  (int-ℕ (minimal-positive-distance-succ-y-coeff x y)))
                (int-ℕ y))) 
            by (ap (λ H → add-ℤ H (neg-ℤ (mul-ℤ 
                (mul-ℤ 
                  (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))) 
                  (int-ℕ (minimal-positive-distance-succ-y-coeff x y)))
                (int-ℕ y))) ) 
                 (ap (λ H → add-ℤ (mul-ℤ 
                (mul-ℤ 
                  (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
                  ((int-ℕ (minimal-positive-distance-succ-x-coeff x y)))) 
              (int-ℕ (succ-ℕ x))) H) (left-unit-law-mul-ℤ (int-ℕ (succ-ℕ x)) ) 
                  ∙ inv (right-distributive-mul-add-ℤ (mul-ℤ 
                  (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
                  (int-ℕ (minimal-positive-distance-succ-x-coeff x y))) one-ℤ (int-ℕ (succ-ℕ x)) )  ))

  dist-eqn : remainder-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x) ＝ 
    dist-ℕ
      (mul-ℕ (add-ℕ 
        (mul-ℕ 
          (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)) 
          (minimal-positive-distance-succ-x-coeff x y)) 1) 
        (succ-ℕ x))
      (mul-ℕ
        (mul-ℕ  
          (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)) 
          (minimal-positive-distance-succ-y-coeff x y)) y)
  dist-eqn = equational-reasoning
    remainder-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)
    ＝ abs-ℤ (int-ℕ (remainder-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))) 
      by (inv (abs-int-ℕ (remainder-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))))
    ＝ dist-ℤ
      (mul-ℤ (add-ℤ 
        (mul-ℤ 
          (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))) 
          (int-ℕ (minimal-positive-distance-succ-x-coeff x y))) 
         one-ℤ) 
        (int-ℕ (succ-ℕ x)))
      (mul-ℤ
        (mul-ℤ 
          (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))) 
          (int-ℕ (minimal-positive-distance-succ-y-coeff x y))) 
        (int-ℕ y))
      by (ap (abs-ℤ) (isolate-rem-eqn ∙ rearrange-arith-eqn))
    ＝ dist-ℤ
      (mul-ℤ (add-ℤ 
        (int-ℕ (mul-ℕ 
          (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)) 
          (minimal-positive-distance-succ-x-coeff x y))) 
         (int-ℕ 1)) 
        (int-ℕ (succ-ℕ x)))
      (mul-ℤ
        (mul-ℤ 
          (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))) 
          (int-ℕ (minimal-positive-distance-succ-y-coeff x y))) 
        (int-ℕ y))
      by (ap (λ H → dist-ℤ
      (mul-ℤ (add-ℤ H (int-ℕ 1)) 
        (int-ℕ (succ-ℕ x)))
      (mul-ℤ
        (mul-ℤ 
          (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))) 
          (int-ℕ (minimal-positive-distance-succ-y-coeff x y))) 
        (int-ℕ y)))
        (mul-int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)) (minimal-positive-distance-succ-x-coeff x y))) 
    ＝ dist-ℤ
      (mul-ℤ (int-ℕ (add-ℕ
        (mul-ℕ 
          (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)) 
          (minimal-positive-distance-succ-x-coeff x y)) 1)) 
        (int-ℕ (succ-ℕ x)))
      (mul-ℤ
        (mul-ℤ 
          (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))) 
          (int-ℕ (minimal-positive-distance-succ-y-coeff x y))) 
        (int-ℕ y))
      by (ap (λ H → dist-ℤ
      (mul-ℤ H (int-ℕ (succ-ℕ x)))
      (mul-ℤ
        (mul-ℤ 
          (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))) 
          (int-ℕ (minimal-positive-distance-succ-y-coeff x y))) 
        (int-ℕ y))) (add-int-ℕ (mul-ℕ 
          (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)) 
          (minimal-positive-distance-succ-x-coeff x y)) 1)) 
    ＝ dist-ℤ
      (int-ℕ (mul-ℕ (add-ℕ
        (mul-ℕ 
          (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)) 
          (minimal-positive-distance-succ-x-coeff x y)) 1) 
        (succ-ℕ x)))
      (mul-ℤ
        (mul-ℤ 
          (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))) 
          (int-ℕ (minimal-positive-distance-succ-y-coeff x y))) 
        (int-ℕ y))
      by (ap (λ H → dist-ℤ H
      (mul-ℤ
        (mul-ℤ 
          (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))) 
          (int-ℕ (minimal-positive-distance-succ-y-coeff x y))) 
        (int-ℕ y)))
        (mul-int-ℕ (add-ℕ
        (mul-ℕ 
          (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)) 
          (minimal-positive-distance-succ-x-coeff x y)) 1) (succ-ℕ x)))
    ＝ dist-ℤ
      (int-ℕ (mul-ℕ (add-ℕ
        (mul-ℕ 
          (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)) 
          (minimal-positive-distance-succ-x-coeff x y)) 1) 
        (succ-ℕ x)))
      (mul-ℤ
        (int-ℕ (mul-ℕ 
          (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)) 
          (minimal-positive-distance-succ-y-coeff x y))) 
        (int-ℕ y))
      by (ap (λ H → dist-ℤ
      (int-ℕ (mul-ℕ (add-ℕ
        (mul-ℕ 
          (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)) 
          (minimal-positive-distance-succ-x-coeff x y)) 1) 
        (succ-ℕ x)))
      (mul-ℤ H (int-ℕ y))) 
      (mul-int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)) (minimal-positive-distance-succ-y-coeff x y))) 
    ＝ dist-ℤ
      (int-ℕ (mul-ℕ (add-ℕ
        (mul-ℕ 
          (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)) 
          (minimal-positive-distance-succ-x-coeff x y)) 1) 
        (succ-ℕ x)))
      (int-ℕ (mul-ℕ
        (mul-ℕ 
          (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)) 
          (minimal-positive-distance-succ-y-coeff x y)) y))
      by (ap (λ H → dist-ℤ
      (int-ℕ (mul-ℕ (add-ℕ
        (mul-ℕ 
          (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)) 
          (minimal-positive-distance-succ-x-coeff x y)) 1) 
        (succ-ℕ x))) H) 
      (mul-int-ℕ (mul-ℕ 
          (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)) 
          (minimal-positive-distance-succ-y-coeff x y)) y)) 
    ＝ dist-ℕ
      (mul-ℕ (add-ℕ 
        (mul-ℕ 
          (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)) 
          (minimal-positive-distance-succ-x-coeff x y)) 1) 
        (succ-ℕ x))
      (mul-ℕ
        (mul-ℕ  
          (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)) 
          (minimal-positive-distance-succ-y-coeff x y)) y)
      by dist-int-ℕ (mul-ℕ (add-ℕ 
        (mul-ℕ 
          (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)) 
          (minimal-positive-distance-succ-x-coeff x y)) 1) 
        (succ-ℕ x)) (mul-ℕ
        (mul-ℕ  
          (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)) 
          (minimal-positive-distance-succ-y-coeff x y)) y)

... | inr tysx = pair (abs-ℤ 
      (add-ℤ (mul-ℤ
          (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
          (int-ℕ (minimal-positive-distance-succ-x-coeff x y))) (neg-ℤ one-ℤ)))
      (pair (mul-ℕ 
      (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))
      (minimal-positive-distance-succ-y-coeff x y)) (inv (dist-eqn)))
  where
  rewrite-dist : add-ℕ (mul-ℕ (minimal-positive-distance-succ-y-coeff x y) y) (minimal-positive-distance (succ-ℕ x) y) ＝ (mul-ℕ (minimal-positive-distance-succ-x-coeff x y) (succ-ℕ x)) 
  rewrite-dist = rewrite-right-dist-add-ℕ 
    (mul-ℕ (minimal-positive-distance-succ-y-coeff x y) y) 
    (minimal-positive-distance (succ-ℕ x) y)
    (mul-ℕ (minimal-positive-distance-succ-x-coeff x y) (succ-ℕ x))
    tysx
    ((inv (minimal-positive-distance-succ-eqn x y))
      ∙ symmetric-dist-ℕ (mul-ℕ (minimal-positive-distance-succ-x-coeff x y) (succ-ℕ x)) (mul-ℕ (minimal-positive-distance-succ-y-coeff x y) y))

  quotient-min-dist-succ-x-nonzero : is-nonzero-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))
  quotient-min-dist-succ-x-nonzero iszero = contradiction-le-ℕ (succ-ℕ x) (minimal-positive-distance (succ-ℕ x) y) le-x-d leq-d-x
    where
    x-r-equality : succ-ℕ x ＝ remainder-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)
    x-r-equality = equational-reasoning
      succ-ℕ x
      ＝ add-ℕ (mul-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)) (minimal-positive-distance (succ-ℕ x) y)) (remainder-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))
        by (inv (eq-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
      ＝ add-ℕ (mul-ℕ 0 (minimal-positive-distance (succ-ℕ x) y)) (remainder-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))
        by (ap (λ H → add-ℕ (mul-ℕ H (minimal-positive-distance (succ-ℕ x) y)) (remainder-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))) iszero)
      ＝ add-ℕ 0 (remainder-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))
        by (ap (λ H → add-ℕ H (remainder-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))) (left-zero-law-mul-ℕ (minimal-positive-distance (succ-ℕ x) y)))
      ＝ remainder-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)
        by (left-unit-law-add-ℕ (remainder-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))) 

    le-x-d : le-ℕ (succ-ℕ x) (minimal-positive-distance (succ-ℕ x) y)
    le-x-d = tr (λ n → le-ℕ n (minimal-positive-distance (succ-ℕ x) y))
      (inv (x-r-equality)) 
      (remainder-min-dist-succ-x-le-min-dist x y)
    
    x-pos-dist : pos-distance-between-multiples (succ-ℕ x) y (succ-ℕ x)
    x-pos-dist H = pair' (is-nonzero-succ-ℕ x) (pair 1 (pair 0 (ap succ-ℕ (left-unit-law-add-ℕ x))))

    leq-d-x : leq-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)
    leq-d-x = minimal-positive-distance-is-minimal (succ-ℕ x) y (succ-ℕ x) 
      x-pos-dist
 
  min-dist-succ-x-coeff-nonzero : is-nonzero-ℕ (minimal-positive-distance-succ-x-coeff x y)
  min-dist-succ-x-coeff-nonzero iszero = minimal-positive-distance-nonzero (succ-ℕ x) y (tr (is-nonzero-ℕ) (inv (left-successor-law-add-ℕ x y)) (is-nonzero-succ-ℕ (add-ℕ x y))) d-is-zero
    where
    zero-addition : add-ℕ (mul-ℕ (minimal-positive-distance-succ-y-coeff x y) y) (minimal-positive-distance (succ-ℕ x) y) ＝ 0
    zero-addition = equational-reasoning
      add-ℕ (mul-ℕ (minimal-positive-distance-succ-y-coeff x y) y) (minimal-positive-distance (succ-ℕ x) y) 
      ＝ (mul-ℕ (minimal-positive-distance-succ-x-coeff x y) (succ-ℕ x))
        by rewrite-dist
      ＝ (mul-ℕ zero-ℕ (succ-ℕ x))
        by (ap (λ H → mul-ℕ H (succ-ℕ x)) iszero)
      ＝ zero-ℕ
      by (left-zero-law-mul-ℕ (succ-ℕ x))

    d-is-zero : is-zero-ℕ (minimal-positive-distance (succ-ℕ x) y)
    d-is-zero = is-zero-right-is-zero-add-ℕ (mul-ℕ (minimal-positive-distance-succ-y-coeff x y) y) (minimal-positive-distance (succ-ℕ x) y) (zero-addition)

  coeff-nonnegative : leq-ℤ one-ℤ (mul-ℤ 
    (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
    (int-ℕ (minimal-positive-distance-succ-x-coeff x y)))
  coeff-nonnegative = tr (λ z → leq-ℤ one-ℤ z) 
    (inv (mul-int-ℕ 
      (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)) 
      (minimal-positive-distance-succ-x-coeff x y)))
    (leq-int-ℕ 1 
      (mul-ℕ 
        (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))
        (minimal-positive-distance-succ-x-coeff x y))
      (leq-succ-le-ℕ 0 
        (mul-ℕ 
          (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))
          (minimal-positive-distance-succ-x-coeff x y))
        (le-is-nonzero-ℕ
          (mul-ℕ 
            (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))
            (minimal-positive-distance-succ-x-coeff x y))
          (is-nonzero-mul-ℕ
            (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))
            (minimal-positive-distance-succ-x-coeff x y)
            quotient-min-dist-succ-x-nonzero
            min-dist-succ-x-coeff-nonzero))))

  add-dist-eqn : int-ℕ (minimal-positive-distance (succ-ℕ x) y) 
    ＝ add-ℤ (mul-ℤ (neg-ℤ (int-ℕ (minimal-positive-distance-succ-y-coeff x y))) (int-ℕ y)) (mul-ℤ (int-ℕ (minimal-positive-distance-succ-x-coeff x y)) (int-ℕ (succ-ℕ x)))
  add-dist-eqn = equational-reasoning
    int-ℕ (minimal-positive-distance (succ-ℕ x) y)
    ＝ add-ℤ (neg-ℤ (int-ℕ (mul-ℕ (minimal-positive-distance-succ-y-coeff x y) y))) (add-ℤ (int-ℕ (mul-ℕ (minimal-positive-distance-succ-y-coeff x y) y)) (int-ℕ (minimal-positive-distance (succ-ℕ x) y))) 
      by (inv (isretr-add-neg-ℤ (int-ℕ (mul-ℕ (minimal-positive-distance-succ-y-coeff x y) y)) (int-ℕ (minimal-positive-distance (succ-ℕ x) y))))
    ＝ add-ℤ (neg-ℤ (int-ℕ (mul-ℕ (minimal-positive-distance-succ-y-coeff x y) y))) (int-ℕ (add-ℕ (mul-ℕ (minimal-positive-distance-succ-y-coeff x y) y) (minimal-positive-distance (succ-ℕ x) y)))
      by (ap (λ H → add-ℤ (neg-ℤ (int-ℕ (mul-ℕ (minimal-positive-distance-succ-y-coeff x y) y))) H) (add-int-ℕ (mul-ℕ (minimal-positive-distance-succ-y-coeff x y) y) (minimal-positive-distance (succ-ℕ x) y)))
    ＝ add-ℤ (neg-ℤ (int-ℕ (mul-ℕ (minimal-positive-distance-succ-y-coeff x y) y))) (int-ℕ (mul-ℕ (minimal-positive-distance-succ-x-coeff x y) (succ-ℕ x))) 
      by (ap (λ H → add-ℤ (neg-ℤ (int-ℕ (mul-ℕ (minimal-positive-distance-succ-y-coeff x y) y))) (int-ℕ H)) rewrite-dist) 
    ＝ add-ℤ (neg-ℤ (mul-ℤ (int-ℕ (minimal-positive-distance-succ-y-coeff x y)) (int-ℕ y))) (int-ℕ (mul-ℕ (minimal-positive-distance-succ-x-coeff x y) (succ-ℕ x))) 
      by (ap (λ H → add-ℤ (neg-ℤ H) (int-ℕ (mul-ℕ (minimal-positive-distance-succ-x-coeff x y) (succ-ℕ x)))) (inv (mul-int-ℕ (minimal-positive-distance-succ-y-coeff x y) y)))
    ＝ add-ℤ (mul-ℤ (neg-ℤ (int-ℕ (minimal-positive-distance-succ-y-coeff x y))) (int-ℕ y)) (int-ℕ (mul-ℕ (minimal-positive-distance-succ-x-coeff x y) (succ-ℕ x))) 
      by (ap (λ H → add-ℤ H (int-ℕ (mul-ℕ (minimal-positive-distance-succ-x-coeff x y) (succ-ℕ x)))) (inv (left-negative-law-mul-ℤ (int-ℕ (minimal-positive-distance-succ-y-coeff x y)) (int-ℕ y))))
    ＝ add-ℤ (mul-ℤ (neg-ℤ (int-ℕ (minimal-positive-distance-succ-y-coeff x y))) (int-ℕ y)) (mul-ℤ (int-ℕ (minimal-positive-distance-succ-x-coeff x y)) (int-ℕ (succ-ℕ x))) 
      by (ap (λ H → add-ℤ (mul-ℤ (neg-ℤ (int-ℕ (minimal-positive-distance-succ-y-coeff x y))) (int-ℕ y)) H) (inv (mul-int-ℕ (minimal-positive-distance-succ-x-coeff x y) (succ-ℕ x)))) 

  isolate-rem-eqn : int-ℕ (remainder-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)) ＝ 
    add-ℤ 
      (neg-ℤ (mul-ℤ 
        (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))) 
        (add-ℤ
           (mul-ℤ (neg-ℤ (int-ℕ (minimal-positive-distance-succ-y-coeff x y))) (int-ℕ y)) 
           (mul-ℤ (int-ℕ (minimal-positive-distance-succ-x-coeff x y)) (int-ℕ (succ-ℕ x))) )))
      (int-ℕ (succ-ℕ x))
  isolate-rem-eqn = 
    equational-reasoning
      (int-ℕ (remainder-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
      ＝ add-ℤ
      (neg-ℤ (mul-ℤ 
        (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))) 
        (add-ℤ
           (mul-ℤ (neg-ℤ (int-ℕ (minimal-positive-distance-succ-y-coeff x y))) (int-ℕ y)) 
           (mul-ℤ ((int-ℕ (minimal-positive-distance-succ-x-coeff x y))) (int-ℕ (succ-ℕ x))) ))) 
      (add-ℤ  
        (mul-ℤ 
          (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))) 
          (add-ℤ
            (mul-ℤ (neg-ℤ (int-ℕ (minimal-positive-distance-succ-y-coeff x y))) (int-ℕ y)) 
            (mul-ℤ (int-ℕ (minimal-positive-distance-succ-x-coeff x y)) (int-ℕ (succ-ℕ x))) )) 
       (int-ℕ (remainder-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))) 
         by (inv (isretr-add-neg-ℤ
           (mul-ℤ 
             (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))) 
             (add-ℤ
               (mul-ℤ (neg-ℤ (int-ℕ (minimal-positive-distance-succ-y-coeff x y))) (int-ℕ y)) 
               (mul-ℤ (int-ℕ (minimal-positive-distance-succ-x-coeff x y)) (int-ℕ (succ-ℕ x))))) (int-ℕ (remainder-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))))
        ＝ add-ℤ
        (neg-ℤ (mul-ℤ 
          (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))) 
          (add-ℤ
           (mul-ℤ (neg-ℤ (int-ℕ (minimal-positive-distance-succ-y-coeff x y))) (int-ℕ y)) 
           (mul-ℤ (int-ℕ (minimal-positive-distance-succ-x-coeff x y)) (int-ℕ (succ-ℕ x))) ))) 
        (add-ℤ  
          (mul-ℤ 
            (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))) 
            (int-ℕ (minimal-positive-distance (succ-ℕ x) y))  ) 
          (int-ℕ (remainder-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))) 
          by (ap (λ H → add-ℤ
          (neg-ℤ (mul-ℤ 
            (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))) 
            (add-ℤ
              (mul-ℤ (neg-ℤ (int-ℕ (minimal-positive-distance-succ-y-coeff x y))) (int-ℕ y)) 
              (mul-ℤ (int-ℕ (minimal-positive-distance-succ-x-coeff x y)) (int-ℕ (succ-ℕ x))) ))) 
          (add-ℤ  
            (mul-ℤ 
              (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))) 
              H) 
            (int-ℕ (remainder-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))))) 
            (inv add-dist-eqn))
        ＝ add-ℤ
        (neg-ℤ (mul-ℤ 
          (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))) 
          (add-ℤ
           (mul-ℤ (neg-ℤ (int-ℕ (minimal-positive-distance-succ-y-coeff x y))) (int-ℕ y)) 
           (mul-ℤ (int-ℕ (minimal-positive-distance-succ-x-coeff x y)) (int-ℕ (succ-ℕ x))) ))) 
        (int-ℕ (succ-ℕ x))
          by (ap (λ H → add-ℤ 
            (neg-ℤ (mul-ℤ 
              (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))) 
            (add-ℤ
               (mul-ℤ (neg-ℤ (int-ℕ (minimal-positive-distance-succ-y-coeff x y))) (int-ℕ y)) 
               (mul-ℤ (int-ℕ (minimal-positive-distance-succ-x-coeff x y)) (int-ℕ (succ-ℕ x))) ))) H) (minimal-positive-distance-div-succ-x-eqn x y))

  rearrange-arith : 
    add-ℤ 
      (neg-ℤ (mul-ℤ 
        (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))) 
        (add-ℤ
           (mul-ℤ (neg-ℤ (int-ℕ (minimal-positive-distance-succ-y-coeff x y))) (int-ℕ y)) 
           (mul-ℤ (int-ℕ (minimal-positive-distance-succ-x-coeff x y)) (int-ℕ (succ-ℕ x))) )))
      (int-ℕ (succ-ℕ x))
    ＝ add-ℤ
      (mul-ℤ 
        (mul-ℤ 
          (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
          (int-ℕ (minimal-positive-distance-succ-y-coeff x y))) 
        (int-ℕ y))
      (neg-ℤ (mul-ℤ
        (add-ℤ (mul-ℤ
          (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
          (int-ℕ (minimal-positive-distance-succ-x-coeff x y))) (neg-ℤ one-ℤ))
        (int-ℕ (succ-ℕ x))))
  rearrange-arith = equational-reasoning
    add-ℤ 
      (neg-ℤ (mul-ℤ 
        (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))) 
        (add-ℤ
           (mul-ℤ (neg-ℤ (int-ℕ (minimal-positive-distance-succ-y-coeff x y))) (int-ℕ y)) 
           (mul-ℤ (int-ℕ (minimal-positive-distance-succ-x-coeff x y)) (int-ℕ (succ-ℕ x))) )))
      (int-ℕ (succ-ℕ x))
    ＝ (add-ℤ 
      (neg-ℤ (add-ℤ 
        (mul-ℤ 
          (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))) 
          (mul-ℤ (neg-ℤ (int-ℕ (minimal-positive-distance-succ-y-coeff x y))) (int-ℕ y))) 
        (mul-ℤ 
          (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
          (mul-ℤ (int-ℕ (minimal-positive-distance-succ-x-coeff x y)) (int-ℕ (succ-ℕ x)))))))
      (int-ℕ (succ-ℕ x))
      by (ap (λ H → add-ℤ (neg-ℤ H) (int-ℕ (succ-ℕ x)))
        (left-distributive-mul-add-ℤ
          (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
          (mul-ℤ (neg-ℤ (int-ℕ (minimal-positive-distance-succ-y-coeff x y))) (int-ℕ y))
          (mul-ℤ (int-ℕ (minimal-positive-distance-succ-x-coeff x y)) (int-ℕ (succ-ℕ x)))))
     ＝ (add-ℤ 
      (neg-ℤ (add-ℤ 
        (mul-ℤ 
          (mul-ℤ 
            (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
            (neg-ℤ (int-ℕ (minimal-positive-distance-succ-y-coeff x y)))) 
          (int-ℕ y)) 
        (mul-ℤ 
          (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
          (mul-ℤ (int-ℕ (minimal-positive-distance-succ-x-coeff x y)) (int-ℕ (succ-ℕ x))))))
         (int-ℕ (succ-ℕ x)))
       by (ap (λ H → (add-ℤ 
        (neg-ℤ (add-ℤ H 
          (mul-ℤ 
            (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
            (mul-ℤ (int-ℕ (minimal-positive-distance-succ-x-coeff x y)) (int-ℕ (succ-ℕ x))))))
        (int-ℕ (succ-ℕ x))))
         (inv (associative-mul-ℤ 
           (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
           (neg-ℤ (int-ℕ (minimal-positive-distance-succ-y-coeff x y)))
           (int-ℕ y))))
      ＝ (add-ℤ 
      (neg-ℤ (add-ℤ 
        (mul-ℤ 
          (mul-ℤ 
            (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
            (neg-ℤ (int-ℕ (minimal-positive-distance-succ-y-coeff x y)))) 
          (int-ℕ y)) 
        (mul-ℤ 
          (mul-ℤ 
            (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
            (int-ℕ (minimal-positive-distance-succ-x-coeff x y)))
          (int-ℕ (succ-ℕ x)))))
         (int-ℕ (succ-ℕ x)))
         by (ap (λ H → (add-ℤ 
          (neg-ℤ (add-ℤ 
            (mul-ℤ 
              (mul-ℤ 
                (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
                (neg-ℤ (int-ℕ (minimal-positive-distance-succ-y-coeff x y)))) 
              (int-ℕ y)) H))
         (int-ℕ (succ-ℕ x))))
           (inv (associative-mul-ℤ 
           (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
           (int-ℕ (minimal-positive-distance-succ-x-coeff x y))
           (int-ℕ (succ-ℕ x)))))  
        ＝ (add-ℤ 
        (neg-ℤ (add-ℤ 
          (mul-ℤ 
            (neg-ℤ (mul-ℤ 
              (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
              (int-ℕ (minimal-positive-distance-succ-y-coeff x y)))) 
            (int-ℕ y)) 
          (mul-ℤ 
            (mul-ℤ 
              (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
              (int-ℕ (minimal-positive-distance-succ-x-coeff x y)))
            (int-ℕ (succ-ℕ x)))))
           (int-ℕ (succ-ℕ x)))
           by (ap (λ H → (add-ℤ 
          (neg-ℤ (add-ℤ 
            (mul-ℤ H (int-ℕ y)) 
            (mul-ℤ 
              (mul-ℤ 
                (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
                (int-ℕ (minimal-positive-distance-succ-x-coeff x y)))
              (int-ℕ (succ-ℕ x)))))
             (int-ℕ (succ-ℕ x)))) 
            (right-negative-law-mul-ℤ 
             (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
             (int-ℕ (minimal-positive-distance-succ-y-coeff x y))))
         ＝ (add-ℤ 
          (add-ℤ 
            (neg-ℤ (mul-ℤ 
              (neg-ℤ (mul-ℤ 
                (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
                (int-ℕ (minimal-positive-distance-succ-y-coeff x y)))) 
              (int-ℕ y))) 
            (neg-ℤ (mul-ℤ 
              (mul-ℤ 
                (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
                (int-ℕ (minimal-positive-distance-succ-x-coeff x y)))
              (int-ℕ (succ-ℕ x)))))
             (int-ℕ (succ-ℕ x)))
            by (ap (λ H → add-ℤ H (int-ℕ (succ-ℕ x))) 
              (distributive-neg-add-ℤ
                (mul-ℤ 
                  (neg-ℤ (mul-ℤ 
                    (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
                    (int-ℕ (minimal-positive-distance-succ-y-coeff x y)))) 
                  (int-ℕ y)) 
                (mul-ℤ 
                  (mul-ℤ 
                    (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
                    (int-ℕ (minimal-positive-distance-succ-x-coeff x y)))
                  (int-ℕ (succ-ℕ x)))))
          ＝ (add-ℤ 
            (add-ℤ 
              (mul-ℤ 
                (neg-ℤ (neg-ℤ (mul-ℤ 
                  (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
                  (int-ℕ (minimal-positive-distance-succ-y-coeff x y))))) 
                (int-ℕ y)) 
              (neg-ℤ (mul-ℤ 
                (mul-ℤ 
                  (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
                  (int-ℕ (minimal-positive-distance-succ-x-coeff x y)))
                (int-ℕ (succ-ℕ x)))))
               (int-ℕ (succ-ℕ x)))
             by (ap (λ H → (add-ℤ 
            (add-ℤ H 
              (neg-ℤ (mul-ℤ 
                (mul-ℤ 
                  (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
                  (int-ℕ (minimal-positive-distance-succ-x-coeff x y)))
                (int-ℕ (succ-ℕ x)))))
               (int-ℕ (succ-ℕ x)))) 
             (inv (left-negative-law-mul-ℤ 
               (neg-ℤ (mul-ℤ 
                  (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
                  (int-ℕ (minimal-positive-distance-succ-y-coeff x y)))) 
               (int-ℕ y))))
          ＝ (add-ℤ 
            (add-ℤ 
              (mul-ℤ 
                (mul-ℤ 
                  (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
                  (int-ℕ (minimal-positive-distance-succ-y-coeff x y))) 
                (int-ℕ y)) 
              (neg-ℤ (mul-ℤ 
                (mul-ℤ 
                  (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
                  (int-ℕ (minimal-positive-distance-succ-x-coeff x y)))
                (int-ℕ (succ-ℕ x)))))
               (int-ℕ (succ-ℕ x)))
              by (ap (λ H → (add-ℤ 
            (add-ℤ 
              (mul-ℤ H (int-ℕ y)) 
              (neg-ℤ (mul-ℤ 
                (mul-ℤ 
                  (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
                  (int-ℕ (minimal-positive-distance-succ-x-coeff x y)))
                (int-ℕ (succ-ℕ x)))))
               (int-ℕ (succ-ℕ x)))) 
             (neg-neg-ℤ (mul-ℤ 
                  (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
                  (int-ℕ (minimal-positive-distance-succ-y-coeff x y))))) 
           ＝ (add-ℤ 
            (add-ℤ 
              (mul-ℤ 
                (mul-ℤ 
                  (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
                  (int-ℕ (minimal-positive-distance-succ-y-coeff x y))) 
                (int-ℕ y)) 
              (mul-ℤ 
                (neg-ℤ (mul-ℤ 
                  (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
                  (int-ℕ (minimal-positive-distance-succ-x-coeff x y))))
                (int-ℕ (succ-ℕ x))))
               (int-ℕ (succ-ℕ x)))
              by (ap (λ H → (add-ℤ 
            (add-ℤ 
              (mul-ℤ 
                (mul-ℤ 
                  (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
                  (int-ℕ (minimal-positive-distance-succ-y-coeff x y))) 
                (int-ℕ y)) H)
               (int-ℕ (succ-ℕ x)))) 
               (inv (left-negative-law-mul-ℤ 
                  (mul-ℤ 
                    (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
                    (int-ℕ (minimal-positive-distance-succ-x-coeff x y)))
                 (int-ℕ (succ-ℕ x)))))
            ＝ (add-ℤ 
              (mul-ℤ 
                (mul-ℤ 
                  (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
                  (int-ℕ (minimal-positive-distance-succ-y-coeff x y))) 
                (int-ℕ y)) 
              (add-ℤ 
                (mul-ℤ 
                  (neg-ℤ (mul-ℤ 
                    (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
                    (int-ℕ (minimal-positive-distance-succ-x-coeff x y))))
                  (int-ℕ (succ-ℕ x)))
               (int-ℕ (succ-ℕ x))))
              by (associative-add-ℤ 
                (mul-ℤ 
                (mul-ℤ 
                  (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
                  (int-ℕ (minimal-positive-distance-succ-y-coeff x y))) 
                (int-ℕ y))
                (mul-ℤ 
                  (neg-ℤ (mul-ℤ 
                    (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
                    (int-ℕ (minimal-positive-distance-succ-x-coeff x y))))
                  (int-ℕ (succ-ℕ x)))
                (int-ℕ (succ-ℕ x)))
             ＝ (add-ℤ 
              (mul-ℤ 
                (mul-ℤ 
                  (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
                  (int-ℕ (minimal-positive-distance-succ-y-coeff x y))) 
                (int-ℕ y)) 
              (add-ℤ 
                (mul-ℤ 
                  (neg-ℤ (mul-ℤ 
                    (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
                    (int-ℕ (minimal-positive-distance-succ-x-coeff x y))))
                  (int-ℕ (succ-ℕ x)))
               (mul-ℤ (neg-ℤ (neg-ℤ one-ℤ)) (int-ℕ (succ-ℕ x)))))
               by (ap (λ H → (add-ℤ 
              (mul-ℤ 
                (mul-ℤ 
                  (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
                  (int-ℕ (minimal-positive-distance-succ-y-coeff x y))) 
                (int-ℕ y)) 
              (add-ℤ 
                (mul-ℤ 
                  (neg-ℤ (mul-ℤ 
                    (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
                    (int-ℕ (minimal-positive-distance-succ-x-coeff x y))))
                  (int-ℕ (succ-ℕ x)))
               (mul-ℤ H (int-ℕ (succ-ℕ x)))))) 
               (inv (neg-neg-ℤ one-ℤ)))
             ＝ (add-ℤ 
              (mul-ℤ 
                (mul-ℤ 
                  (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
                  (int-ℕ (minimal-positive-distance-succ-y-coeff x y))) 
                (int-ℕ y)) 
              (mul-ℤ 
                (add-ℤ  
                  (neg-ℤ (mul-ℤ 
                    (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
                    (int-ℕ (minimal-positive-distance-succ-x-coeff x y))))
               (neg-ℤ (neg-ℤ one-ℤ))) (int-ℕ (succ-ℕ x))))
               by (ap (λ H → (add-ℤ 
              (mul-ℤ 
                (mul-ℤ 
                  (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
                  (int-ℕ (minimal-positive-distance-succ-y-coeff x y))) 
                (int-ℕ y)) H))
               (inv (right-distributive-mul-add-ℤ
                 (neg-ℤ (mul-ℤ 
                    (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
                    (int-ℕ (minimal-positive-distance-succ-x-coeff x y))))
                  (neg-ℤ (neg-ℤ one-ℤ)) (int-ℕ (succ-ℕ x)))))
              ＝ (add-ℤ 
              (mul-ℤ 
                (mul-ℤ 
                  (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
                  (int-ℕ (minimal-positive-distance-succ-y-coeff x y))) 
                (int-ℕ y)) 
              (mul-ℤ 
                (neg-ℤ (add-ℤ  
                  (mul-ℤ 
                    (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
                    (int-ℕ (minimal-positive-distance-succ-x-coeff x y)))
               (neg-ℤ one-ℤ))) (int-ℕ (succ-ℕ x))))
                by (ap (λ H → (add-ℤ 
              (mul-ℤ 
                (mul-ℤ 
                  (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
                  (int-ℕ (minimal-positive-distance-succ-y-coeff x y))) 
                (int-ℕ y)) 
              (mul-ℤ H (int-ℕ (succ-ℕ x)))))
              (inv (distributive-neg-add-ℤ (mul-ℤ 
                    (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
                    (int-ℕ (minimal-positive-distance-succ-x-coeff x y))) 
                   (neg-ℤ one-ℤ))))
              ＝ (add-ℤ 
              (mul-ℤ 
                (mul-ℤ 
                  (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
                  (int-ℕ (minimal-positive-distance-succ-y-coeff x y))) 
                (int-ℕ y)) 
              (neg-ℤ (mul-ℤ 
                (add-ℤ  
                  (mul-ℤ 
                    (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
                    (int-ℕ (minimal-positive-distance-succ-x-coeff x y)))
               (neg-ℤ one-ℤ)) (int-ℕ (succ-ℕ x)))))
                by (ap (λ H → (add-ℤ 
              (mul-ℤ 
                (mul-ℤ 
                  (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
                  (int-ℕ (minimal-positive-distance-succ-y-coeff x y))) 
                (int-ℕ y)) H)) 
                (left-negative-law-mul-ℤ (add-ℤ  
                  (mul-ℤ 
                    (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
                    (int-ℕ (minimal-positive-distance-succ-x-coeff x y)))
               (neg-ℤ one-ℤ))
               (int-ℕ (succ-ℕ x))))  

  dist-eqn : remainder-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)
    ＝ dist-ℕ
    (mul-ℕ (abs-ℤ 
      (add-ℤ (mul-ℤ
          (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
          (int-ℕ (minimal-positive-distance-succ-x-coeff x y))) (neg-ℤ one-ℤ))) (succ-ℕ x))
    (mul-ℕ (mul-ℕ 
      (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))
      (minimal-positive-distance-succ-y-coeff x y)) y)
  dist-eqn = equational-reasoning
    remainder-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)
    ＝ abs-ℤ (int-ℕ (remainder-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))) 
      by (inv (abs-int-ℕ (remainder-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))))
    ＝ abs-ℤ (add-ℤ
      (mul-ℤ 
        (mul-ℤ 
          (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
          (int-ℕ (minimal-positive-distance-succ-y-coeff x y))) 
        (int-ℕ y))
      (neg-ℤ (mul-ℤ
        (add-ℤ (mul-ℤ
          (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
          (int-ℕ (minimal-positive-distance-succ-x-coeff x y))) (neg-ℤ one-ℤ))
        (int-ℕ (succ-ℕ x)))))
       by (ap abs-ℤ (isolate-rem-eqn ∙ rearrange-arith))
    ＝ (dist-ℤ
      (mul-ℤ 
        (int-ℕ (mul-ℕ 
          (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))
          (minimal-positive-distance-succ-y-coeff x y))) 
        (int-ℕ y))
       (mul-ℤ
        (add-ℤ (mul-ℤ
          (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
          (int-ℕ (minimal-positive-distance-succ-x-coeff x y))) (neg-ℤ one-ℤ))
        (int-ℕ (succ-ℕ x)))) 
       by (ap (λ H → (dist-ℤ
      (mul-ℤ H (int-ℕ y))
       (mul-ℤ
        (add-ℤ (mul-ℤ
          (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
          (int-ℕ (minimal-positive-distance-succ-x-coeff x y))) (neg-ℤ one-ℤ))
        (int-ℕ (succ-ℕ x))))) 
         (mul-int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)) (minimal-positive-distance-succ-y-coeff x y)))  
      ＝ (dist-ℤ
      (int-ℕ (mul-ℕ 
        (mul-ℕ 
          (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))
          (minimal-positive-distance-succ-y-coeff x y)) y))
       (mul-ℤ
        (add-ℤ (mul-ℤ
          (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
          (int-ℕ (minimal-positive-distance-succ-x-coeff x y))) (neg-ℤ one-ℤ))
        (int-ℕ (succ-ℕ x))))
        by (ap (λ H → (dist-ℤ H (mul-ℤ
        (add-ℤ (mul-ℤ
          (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
          (int-ℕ (minimal-positive-distance-succ-x-coeff x y))) (neg-ℤ one-ℤ))
        (int-ℕ (succ-ℕ x))))) 
          (mul-int-ℕ (mul-ℕ 
          (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))
          (minimal-positive-distance-succ-y-coeff x y)) y))
      ＝ (dist-ℤ
      (int-ℕ (mul-ℕ 
        (mul-ℕ 
          (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))
          (minimal-positive-distance-succ-y-coeff x y)) y))
       (mul-ℤ
        (int-ℕ (abs-ℤ (add-ℤ (mul-ℤ
          (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
          (int-ℕ (minimal-positive-distance-succ-x-coeff x y))) (neg-ℤ one-ℤ))))
        (int-ℕ (succ-ℕ x))))
        by (ap (λ H → (dist-ℤ
      (int-ℕ (mul-ℕ 
        (mul-ℕ 
          (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))
          (minimal-positive-distance-succ-y-coeff x y)) y))
       (mul-ℤ H (int-ℕ (succ-ℕ x)))))
          (inv (int-abs-is-nonnegative-ℤ 
            (add-ℤ (mul-ℤ
              (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
              (int-ℕ (minimal-positive-distance-succ-x-coeff x y))) (neg-ℤ one-ℤ)) coeff-nonnegative)))
      ＝ (dist-ℤ
      (int-ℕ (mul-ℕ 
        (mul-ℕ 
          (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))
          (minimal-positive-distance-succ-y-coeff x y)) y))
       (int-ℕ (mul-ℕ
        (abs-ℤ (add-ℤ (mul-ℤ
          (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
          (int-ℕ (minimal-positive-distance-succ-x-coeff x y))) (neg-ℤ one-ℤ)))
        (succ-ℕ x))))
        by (ap (λ H → (dist-ℤ
      (int-ℕ (mul-ℕ 
        (mul-ℕ 
          (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))
          (minimal-positive-distance-succ-y-coeff x y)) y)) H))
        (mul-int-ℕ (abs-ℤ (add-ℤ (mul-ℤ
          (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
          (int-ℕ (minimal-positive-distance-succ-x-coeff x y))) (neg-ℤ one-ℤ))) (succ-ℕ x))) 
      ＝ (dist-ℕ
      (mul-ℕ 
        (mul-ℕ 
          (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))
          (minimal-positive-distance-succ-y-coeff x y)) y)
       (mul-ℕ
        (abs-ℤ (add-ℤ (mul-ℤ
          (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
          (int-ℕ (minimal-positive-distance-succ-x-coeff x y))) (neg-ℤ one-ℤ)))
        (succ-ℕ x))) 
         by (dist-int-ℕ 
           (mul-ℕ 
             (mul-ℕ 
               (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))
               (minimal-positive-distance-succ-y-coeff x y)) y)
             (mul-ℕ
               (abs-ℤ (add-ℤ (mul-ℤ
                 (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
                 (int-ℕ (minimal-positive-distance-succ-x-coeff x y))) (neg-ℤ one-ℤ)))
               (succ-ℕ x)))
       ＝ (dist-ℕ 
       (mul-ℕ
        (abs-ℤ (add-ℤ (mul-ℤ
          (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
          (int-ℕ (minimal-positive-distance-succ-x-coeff x y))) (neg-ℤ one-ℤ)))
        (succ-ℕ x))
       (mul-ℕ 
        (mul-ℕ 
          (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))
          (minimal-positive-distance-succ-y-coeff x y)) y)) 
         by (symmetric-dist-ℕ
           (mul-ℕ 
        (mul-ℕ 
          (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))
          (minimal-positive-distance-succ-y-coeff x y)) y)
           (mul-ℕ
        (abs-ℤ (add-ℤ (mul-ℤ
          (int-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
          (int-ℕ (minimal-positive-distance-succ-x-coeff x y))) (neg-ℤ one-ℤ)))
        (succ-ℕ x))) 

remainder-min-dist-succ-x-not-is-nonzero : (x y : ℕ) → ¬ (is-nonzero-ℕ (remainder-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)))
remainder-min-dist-succ-x-not-is-nonzero x y nonzero = contradiction-le-ℕ
  (remainder-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))
  (minimal-positive-distance (succ-ℕ x) y) 
  (remainder-min-dist-succ-x-le-min-dist x y) d-leq-rem
  where
  rem-pos-dist : pos-distance-between-multiples (succ-ℕ x) y (remainder-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))
  rem-pos-dist H = pair' nonzero (remainder-min-dist-succ-x-is-distance x y)

  d-leq-rem : leq-ℕ (minimal-positive-distance (succ-ℕ x) y) (remainder-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)) 
  d-leq-rem = minimal-positive-distance-is-minimal (succ-ℕ x) y 
    (remainder-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)) 
    rem-pos-dist

remainder-min-dist-succ-x-is-zero : (x y : ℕ) → is-zero-ℕ (remainder-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)) 
remainder-min-dist-succ-x-is-zero x y with is-decidable-is-zero-ℕ (remainder-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))
... | inl z = z
... | inr nz = ex-falso (remainder-min-dist-succ-x-not-is-nonzero x y nz) 


minimal-positive-distance-div-fst : (x y : ℕ) → div-ℕ (minimal-positive-distance x y) x
minimal-positive-distance-div-fst zero-ℕ y = pair zero-ℕ (left-zero-law-mul-ℕ (minimal-positive-distance zero-ℕ y))
minimal-positive-distance-div-fst (succ-ℕ x) y = pair (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)) eqn
  where 
  eqn : mul-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)) (minimal-positive-distance (succ-ℕ x) y) ＝ (succ-ℕ x)
  eqn = 
    equational-reasoning
      mul-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)) (minimal-positive-distance (succ-ℕ x) y)
      ＝ add-ℕ (mul-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)) (minimal-positive-distance (succ-ℕ x) y)) zero-ℕ 
        by (inv (right-unit-law-add-ℕ (mul-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)) (minimal-positive-distance (succ-ℕ x) y)) ))
      ＝ add-ℕ (mul-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)) (minimal-positive-distance (succ-ℕ x) y)) (remainder-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))
        by (ap (λ H → add-ℕ (mul-ℕ (quotient-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)) (minimal-positive-distance (succ-ℕ x) y)) H) (inv (remainder-min-dist-succ-x-is-zero x y)))
      ＝ succ-ℕ x by eq-euclidean-division-ℕ (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)

minimal-positive-distance-div-snd : (x y : ℕ) → div-ℕ (minimal-positive-distance x y) y
minimal-positive-distance-div-snd x y = concatenate-eq-div-ℕ (minimal-positive-distance-sym x y) (minimal-positive-distance-div-fst y x) 

minimal-positive-distance-div-gcd-ℕ : (x y : ℕ) → div-ℕ (minimal-positive-distance x y) (gcd-ℕ x y)
minimal-positive-distance-div-gcd-ℕ x y = div-gcd-is-common-divisor-ℕ x y (minimal-positive-distance x y) (pair' (minimal-positive-distance-div-fst x y) (minimal-positive-distance-div-snd x y)) 

gcd-ℕ-div-x-mults : (x y z : ℕ) → (d : is-distance-between-multiples-ℕ x y z) → div-ℕ (gcd-ℕ x y) (mul-ℕ (is-distance-between-multiples-fst-coeff-ℕ d) x)
gcd-ℕ-div-x-mults x y z d = div-mul-ℕ 
  (is-distance-between-multiples-fst-coeff-ℕ d) 
  (gcd-ℕ x y) x (pr1 (is-common-divisor-gcd-ℕ x y))

gcd-ℕ-div-y-mults : (x y z : ℕ) → (d : is-distance-between-multiples-ℕ x y z) → div-ℕ (gcd-ℕ x y) (mul-ℕ (is-distance-between-multiples-snd-coeff-ℕ d) y)
gcd-ℕ-div-y-mults x y z d = div-mul-ℕ 
  (is-distance-between-multiples-snd-coeff-ℕ d) 
  (gcd-ℕ x y) y (pr2 (is-common-divisor-gcd-ℕ x y))

gcd-ℕ-div-dist-between-mult : (x y z : ℕ) → is-distance-between-multiples-ℕ x y z → div-ℕ (gcd-ℕ x y) z 
gcd-ℕ-div-dist-between-mult x y z dist
  with decide-leq-ℕ (mul-ℕ (is-distance-between-multiples-fst-coeff-ℕ dist) x) (mul-ℕ (is-distance-between-multiples-snd-coeff-ℕ dist) y)
... | inl sxty = div-right-summand-ℕ (gcd-ℕ x y)
  (mul-ℕ (is-distance-between-multiples-fst-coeff-ℕ dist) x)
  z
  (gcd-ℕ-div-x-mults x y z dist)
  (concatenate-div-eq-ℕ (gcd-ℕ-div-y-mults x y z dist) (inv rewrite-dist))
  where
  rewrite-dist : add-ℕ (mul-ℕ (is-distance-between-multiples-fst-coeff-ℕ dist) x) z ＝ mul-ℕ (is-distance-between-multiples-snd-coeff-ℕ dist) y 
  rewrite-dist = rewrite-right-dist-add-ℕ  
    (mul-ℕ (is-distance-between-multiples-fst-coeff-ℕ dist) x)
    z
    (mul-ℕ (is-distance-between-multiples-snd-coeff-ℕ dist) y)
    sxty
    (inv (is-distance-between-multiples-eqn-ℕ dist))

... | inr tysx = div-right-summand-ℕ (gcd-ℕ x y)
  (mul-ℕ (is-distance-between-multiples-snd-coeff-ℕ dist) y)
  z
  (gcd-ℕ-div-y-mults x y z dist)
  (concatenate-div-eq-ℕ (gcd-ℕ-div-x-mults x y z dist) (inv rewrite-dist)) 
  where
  rewrite-dist : add-ℕ (mul-ℕ (is-distance-between-multiples-snd-coeff-ℕ dist) y) z ＝ mul-ℕ (is-distance-between-multiples-fst-coeff-ℕ dist) x 
  rewrite-dist = rewrite-right-dist-add-ℕ  
    (mul-ℕ (is-distance-between-multiples-snd-coeff-ℕ dist) y)
    z
    (mul-ℕ (is-distance-between-multiples-fst-coeff-ℕ dist) x)
    tysx
    (inv (is-distance-between-multiples-eqn-ℕ dist) 
      ∙ symmetric-dist-ℕ (mul-ℕ (is-distance-between-multiples-fst-coeff-ℕ dist) x) (mul-ℕ (is-distance-between-multiples-snd-coeff-ℕ dist) y))

  div-gcd-x : div-ℕ (gcd-ℕ x y) (mul-ℕ (is-distance-between-multiples-fst-coeff-ℕ dist) x)
  div-gcd-x = div-mul-ℕ 
    (is-distance-between-multiples-fst-coeff-ℕ dist) 
    (gcd-ℕ x y) x (pr1 (is-common-divisor-gcd-ℕ x y))

gcd-ℕ-div-minimal-positive-distance : (x y : ℕ) → is-nonzero-ℕ (add-ℕ x y) → div-ℕ (gcd-ℕ x y) (minimal-positive-distance x y)
gcd-ℕ-div-minimal-positive-distance x y H = gcd-ℕ-div-dist-between-mult x y (minimal-positive-distance x y) (minimal-positive-distance-is-distance x y H)  

bezouts-lemma-ℕ : (x y : ℕ) → is-nonzero-ℕ (add-ℕ x y) → minimal-positive-distance x y ＝ gcd-ℕ x y
bezouts-lemma-ℕ x y H = antisymmetric-div-ℕ (minimal-positive-distance x y) (gcd-ℕ x y) (minimal-positive-distance-div-gcd-ℕ x y) (gcd-ℕ-div-minimal-positive-distance x y H)   

bezouts-lemma-eqn-ℕ : (x y : ℕ) → (H : is-nonzero-ℕ (add-ℕ x y)) → dist-ℕ (mul-ℕ (minimal-positive-distance-x-coeff x y H) x) (mul-ℕ (minimal-positive-distance-y-coeff x y H) y) ＝ gcd-ℕ x y
bezouts-lemma-eqn-ℕ x y H = minimal-positive-distance-eqn x y H ∙ bezouts-lemma-ℕ x y H
```
## Bezout's Lemma on `ℤ`
```agda
bezouts-lemma-eqn-to-int : 
  (x y : ℤ) → (H : is-nonzero-ℕ (add-ℕ (abs-ℤ x) (abs-ℤ y))) 
    → nat-gcd-ℤ x y ＝ 
      dist-ℕ 
        (abs-ℤ (mul-ℤ (int-ℕ (minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) H)) x)) 
        (abs-ℤ (mul-ℤ (int-ℕ (minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) H)) y))
bezouts-lemma-eqn-to-int x y H = 
  equational-reasoning
    nat-gcd-ℤ x y 
    ＝ dist-ℕ (mul-ℕ (minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) H) (abs-ℤ x)) (mul-ℕ (minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) H) (abs-ℤ y)) 
      by (inv (bezouts-lemma-eqn-ℕ (abs-ℤ x) (abs-ℤ y) H))
    ＝ dist-ℕ 
        (mul-ℕ (abs-ℤ (int-ℕ (minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) H))) (abs-ℤ x)) 
        (mul-ℕ (minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) H) (abs-ℤ y))
      by (ap (λ K → dist-ℕ 
        (mul-ℕ K (abs-ℤ x)) 
        (mul-ℕ (minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) H) (abs-ℤ y))) 
        (inv (abs-int-ℕ (minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) H))))
    ＝ dist-ℕ 
        (mul-ℕ (abs-ℤ (int-ℕ (minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) H))) (abs-ℤ x)) 
        (mul-ℕ (abs-ℤ (int-ℕ (minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) H))) (abs-ℤ y))
      by (ap (λ K → dist-ℕ 
        (mul-ℕ (abs-ℤ (int-ℕ (minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) H))) (abs-ℤ x))
        (mul-ℕ K (abs-ℤ y)))
        (inv (abs-int-ℕ (minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) H))))
    ＝ dist-ℕ 
        (abs-ℤ (mul-ℤ (int-ℕ (minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) H)) x)) 
        (mul-ℕ (abs-ℤ (int-ℕ (minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) H))) (abs-ℤ y))
      by (ap (λ K → dist-ℕ K (mul-ℕ (abs-ℤ (int-ℕ (minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) H))) (abs-ℤ y)))
      (inv (multiplicative-abs-ℤ (int-ℕ (minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) H)) x)))
    ＝ dist-ℕ 
        (abs-ℤ (mul-ℤ (int-ℕ (minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) H)) x)) 
        (abs-ℤ (mul-ℤ (int-ℕ (minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) H)) y))
      by (ap (λ K → dist-ℕ (abs-ℤ (mul-ℤ (int-ℕ (minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) H)) x)) K) 
      (inv (multiplicative-abs-ℤ (int-ℕ (minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) H)) y))) 

refactor-pos-cond : (x y : ℤ) → (H : is-positive-ℤ x) → (K : is-positive-ℤ y) → is-nonzero-ℕ (add-ℕ (abs-ℤ x) (abs-ℤ y))
refactor-pos-cond x y H K = (λ F → (is-nonzero-abs-ℤ x H) (is-zero-left-is-zero-add-ℕ (abs-ℤ x) (abs-ℤ y) F))

bezouts-lemma-refactor-hypotheses : (x y : ℤ) → (H : is-positive-ℤ x) → (K : is-positive-ℤ y)
  → nat-gcd-ℤ x y ＝ 
      abs-ℤ (diff-ℤ 
        (mul-ℤ (int-ℕ (minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) (refactor-pos-cond x y H K))) x) 
        (mul-ℤ (int-ℕ (minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) (refactor-pos-cond x y H K))) y))
bezouts-lemma-refactor-hypotheses x y H K = (equational-reasoning
    nat-gcd-ℤ x y
    ＝ dist-ℕ 
        (abs-ℤ (mul-ℤ (int-ℕ (minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) P)) x)) 
        (abs-ℤ (mul-ℤ (int-ℕ (minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) P)) y))
      by bezouts-lemma-eqn-to-int x y P 
    ＝ dist-ℤ 
        (mul-ℤ (int-ℕ (minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) P)) x) 
        (mul-ℤ (int-ℕ (minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) P)) y)
      by dist-abs-ℤ
        (mul-ℤ (int-ℕ (minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) P)) x)
        (mul-ℤ (int-ℕ (minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) P)) y)
        x-prod-nonneg y-prod-nonneg) 
  where
  P : is-nonzero-ℕ (add-ℕ (abs-ℤ x) (abs-ℤ y))
  P = (refactor-pos-cond x y H K)
  x-prod-nonneg : is-nonnegative-ℤ (mul-ℤ (int-ℕ (minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) P)) x)
  x-prod-nonneg = is-nonnegative-mul-ℤ
    (is-nonnegative-int-ℕ (minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) P)) 
    (is-nonnegative-is-positive-ℤ H)
  y-prod-nonneg : is-nonnegative-ℤ (mul-ℤ (int-ℕ (minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) P)) y)
  y-prod-nonneg = is-nonnegative-mul-ℤ
    (is-nonnegative-int-ℕ (minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) P)) 
    (is-nonnegative-is-positive-ℤ K)

-- refactor H, maybe just make x and y both positive? 
bezouts-lemma-pos-ints : (x y : ℤ) → (H : is-positive-ℤ x) → (K : is-positive-ℤ y) → Σ ℤ (λ s → Σ ℤ (λ t → add-ℤ (mul-ℤ s x) (mul-ℤ t y) ＝ gcd-ℤ x y))
bezouts-lemma-pos-ints x y H K with 
  (decide-is-nonnegative-ℤ {diff-ℤ 
    (mul-ℤ (int-ℕ (minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) (refactor-pos-cond x y H K))) x) 
    (mul-ℤ (int-ℕ (minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) (refactor-pos-cond x y H K))) y)})
... | inl pos = pair 
    (int-ℕ (minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) (refactor-pos-cond x y H K)))
    (pair (neg-ℤ (int-ℕ (minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) (refactor-pos-cond x y H K)))) 
    (inv eqn))
  where
  eqn : gcd-ℤ x y ＝ 
    (add-ℤ 
        (mul-ℤ (int-ℕ (minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) (refactor-pos-cond x y H K))) x) 
        (mul-ℤ (neg-ℤ (int-ℕ (minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) (refactor-pos-cond x y H K)))) y))
  eqn = equational-reasoning
    gcd-ℤ x y
    ＝ int-ℕ (abs-ℤ (diff-ℤ 
    (mul-ℤ (int-ℕ (minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) (refactor-pos-cond x y H K))) x) 
    (mul-ℤ (int-ℕ (minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) (refactor-pos-cond x y H K))) y)))
    by (ap int-ℕ (bezouts-lemma-refactor-hypotheses x y H K))
    ＝ (diff-ℤ 
    (mul-ℤ (int-ℕ (minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) (refactor-pos-cond x y H K))) x) 
    (mul-ℤ (int-ℕ (minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) (refactor-pos-cond x y H K))) y)) 
    by int-abs-is-nonnegative-ℤ (diff-ℤ 
    (mul-ℤ (int-ℕ (minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) (refactor-pos-cond x y H K))) x) 
    (mul-ℤ (int-ℕ (minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) (refactor-pos-cond x y H K))) y)) pos
    ＝ (add-ℤ 
        (mul-ℤ (int-ℕ (minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) (refactor-pos-cond x y H K))) x) 
        (mul-ℤ (neg-ℤ (int-ℕ (minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) (refactor-pos-cond x y H K)))) y)) 
    by (ap (λ M → add-ℤ (mul-ℤ (int-ℕ (minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) (refactor-pos-cond x y H K))) x) M) 
      (inv (left-negative-law-mul-ℤ (int-ℕ (minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) (refactor-pos-cond x y H K))) y)))
... | inr neg = pair (neg-ℤ (int-ℕ (minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) (refactor-pos-cond x y H K))))
  (pair (int-ℕ (minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) (refactor-pos-cond x y H K))) 
  (inv eqn))
  where 
  eqn : gcd-ℤ x y ＝
    (add-ℤ 
        (mul-ℤ (neg-ℤ (int-ℕ (minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) (refactor-pos-cond x y H K)))) x) 
        (mul-ℤ (int-ℕ (minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) (refactor-pos-cond x y H K))) y))
  eqn = equational-reasoning
    gcd-ℤ x y
    ＝ int-ℕ (abs-ℤ (diff-ℤ 
    (mul-ℤ (int-ℕ (minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) (refactor-pos-cond x y H K))) x) 
    (mul-ℤ (int-ℕ (minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) (refactor-pos-cond x y H K))) y)))
    by (ap int-ℕ (bezouts-lemma-refactor-hypotheses x y H K))
    ＝ int-ℕ (abs-ℤ (neg-ℤ (diff-ℤ 
    (mul-ℤ (int-ℕ (minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) (refactor-pos-cond x y H K))) x) 
    (mul-ℤ (int-ℕ (minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) (refactor-pos-cond x y H K))) y))))
    by (ap (λ M → int-ℕ M) (inv (abs-neg-ℤ (diff-ℤ 
    (mul-ℤ (int-ℕ (minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) (refactor-pos-cond x y H K))) x) 
    (mul-ℤ (int-ℕ (minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) (refactor-pos-cond x y H K))) y)))))
    ＝ (neg-ℤ (diff-ℤ 
    (mul-ℤ (int-ℕ (minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) (refactor-pos-cond x y H K))) x) 
    (mul-ℤ (int-ℕ (minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) (refactor-pos-cond x y H K))) y))) 
    by int-abs-is-nonnegative-ℤ (neg-ℤ (diff-ℤ 
    (mul-ℤ (int-ℕ (minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) (refactor-pos-cond x y H K))) x) 
    (mul-ℤ (int-ℕ (minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) (refactor-pos-cond x y H K))) y))) neg
    ＝ add-ℤ (neg-ℤ (mul-ℤ (int-ℕ (minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) (refactor-pos-cond x y H K))) x))
    (neg-ℤ (neg-ℤ (mul-ℤ (int-ℕ (minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) (refactor-pos-cond x y H K))) y))) 
    by (distributive-neg-add-ℤ 
      (mul-ℤ (int-ℕ (minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) (refactor-pos-cond x y H K))) x)
      (neg-ℤ (mul-ℤ (int-ℕ (minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) (refactor-pos-cond x y H K))) y)))
    ＝ add-ℤ (mul-ℤ (neg-ℤ (int-ℕ (minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) (refactor-pos-cond x y H K)))) x)
    (neg-ℤ (neg-ℤ (mul-ℤ (int-ℕ (minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) (refactor-pos-cond x y H K))) y))) 
    by (ap (λ M → add-ℤ M (neg-ℤ (neg-ℤ (mul-ℤ (int-ℕ (minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) (refactor-pos-cond x y H K))) y)))) 
      (inv (left-negative-law-mul-ℤ (int-ℕ (minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) (refactor-pos-cond x y H K))) x))) 
    ＝ add-ℤ (mul-ℤ (neg-ℤ (int-ℕ (minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) (refactor-pos-cond x y H K)))) x)
    (mul-ℤ (int-ℕ (minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) (refactor-pos-cond x y H K))) y) 
    by (ap (λ M → add-ℤ (mul-ℤ (neg-ℤ (int-ℕ (minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) (refactor-pos-cond x y H K)))) x) M)
      (neg-neg-ℤ (mul-ℤ (int-ℕ (minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) (refactor-pos-cond x y H K))) y)))


bezouts-lemma-ℤ : (x y : ℤ) → Σ ℤ (λ s → Σ ℤ (λ t → add-ℤ (mul-ℤ s x) (mul-ℤ t y) ＝ gcd-ℤ x y))
bezouts-lemma-ℤ (inl x) (inl y) = pair (neg-ℤ s) (pair (neg-ℤ t) eqn)
  where
  pos-bezout : Σ ℤ (λ s → Σ ℤ (λ t → add-ℤ (mul-ℤ s (inr (inr x))) (mul-ℤ t (inr (inr y))) ＝ gcd-ℤ (inr (inr x)) (inr (inr y))))
  pos-bezout = bezouts-lemma-pos-ints (inr (inr x)) (inr (inr y)) star star
  s : ℤ 
  s = pr1 (pos-bezout)
  t : ℤ 
  t = pr1 (pr2 (pos-bezout))
  eqn : add-ℤ (mul-ℤ (neg-ℤ s) (inl x)) (mul-ℤ (neg-ℤ t) (inl y)) ＝ gcd-ℤ (inl x) (inl y)
  eqn = equational-reasoning
    add-ℤ (mul-ℤ (neg-ℤ s) (neg-ℤ (inr (inr x)))) (mul-ℤ (neg-ℤ t) (neg-ℤ (inr (inr y))))
    ＝ add-ℤ (mul-ℤ s (inr (inr x))) (mul-ℤ (neg-ℤ t) (neg-ℤ (inr (inr y))))
    by (ap (λ M → add-ℤ M (mul-ℤ (neg-ℤ t) (neg-ℤ (inr (inr y)))))
      (double-negative-law-mul-ℤ s (inr (inr x))))
    ＝ add-ℤ (mul-ℤ s (inr (inr x))) (mul-ℤ t (inr (inr y)))
    by (ap (λ M → add-ℤ (mul-ℤ s (inr (inr x))) M) (double-negative-law-mul-ℤ t (inr (inr y))))
    ＝ gcd-ℤ (inr (inr x)) (inr (inr y)) by pr2 (pr2 (pos-bezout))
    ＝ gcd-ℤ (inl x) (inr (inr y)) by ap (λ M → (int-ℕ (gcd-ℕ M (succ-ℕ y)))) (abs-neg-ℤ (inr (inr x)))
    ＝ gcd-ℤ (inl x) (inl y) by ap (λ M → (int-ℕ (gcd-ℕ (succ-ℕ x) M))) (abs-neg-ℤ (inr (inr y)))
bezouts-lemma-ℤ (inl x) (inr (inl star)) = pair neg-one-ℤ (pair one-ℤ eqn)
  where
  eqn : add-ℤ (mul-ℤ neg-one-ℤ (inl x)) (mul-ℤ one-ℤ (inr (inl star))) ＝ gcd-ℤ (inl x) (inr (inl star))
  eqn = equational-reasoning
    add-ℤ (mul-ℤ neg-one-ℤ (inl x)) (mul-ℤ one-ℤ (inr (inl star)))
    ＝ add-ℤ (inr (inr x)) (mul-ℤ one-ℤ (inr (inl star)))
    by ap (λ M → add-ℤ M (mul-ℤ one-ℤ (inr (inl star)))) (inv (is-mul-neg-one-neg-ℤ (inl x)))
    ＝ add-ℤ (inr (inr x)) zero-ℤ by ap (λ M → add-ℤ (inr (inr x)) M) (right-zero-law-mul-ℤ one-ℤ)
    ＝ int-ℕ (abs-ℤ (inl x)) by right-unit-law-add-ℤ (inr (inr x))
    ＝ gcd-ℤ (inl x) zero-ℤ by inv (is-id-is-gcd-zero-ℤ' {inl x} {gcd-ℤ (inl x) zero-ℤ} refl)
bezouts-lemma-ℤ (inl x) (inr (inr y)) = pair (neg-ℤ s) (pair t eqn)
  where
  pos-bezout : Σ ℤ (λ s → Σ ℤ (λ t → add-ℤ (mul-ℤ s (inr (inr x))) (mul-ℤ t (inr (inr y))) ＝ gcd-ℤ (inr (inr x)) (inr (inr y))))
  pos-bezout = bezouts-lemma-pos-ints (inr (inr x)) (inr (inr y)) star star
  s : ℤ 
  s = pr1 (pos-bezout)
  t : ℤ 
  t = pr1 (pr2 (pos-bezout))
  eqn : add-ℤ (mul-ℤ (neg-ℤ s) (inl x)) (mul-ℤ t (inr (inr y))) ＝ gcd-ℤ (inl x) (inr (inr y))
  eqn = equational-reasoning
    add-ℤ (mul-ℤ (neg-ℤ s) (neg-ℤ (inr (inr x)))) (mul-ℤ t (inr (inr y)))
    ＝ add-ℤ (mul-ℤ s (inr (inr x))) (mul-ℤ t (inr (inr y)))
    by ap (λ M → add-ℤ M (mul-ℤ t (inr (inr y))))
      (double-negative-law-mul-ℤ s (inr (inr x)))
    ＝ gcd-ℤ (inr (inr x)) (inr (inr y)) by pr2 (pr2 (pos-bezout))
    ＝ gcd-ℤ (inl x) (inr (inr y)) by ap (λ M → (int-ℕ (gcd-ℕ M (succ-ℕ y)))) (abs-neg-ℤ (inr (inr x))) 
bezouts-lemma-ℤ (inr (inl star)) (inl y) = pair one-ℤ (pair neg-one-ℤ eqn)
  where
  eqn : add-ℤ (mul-ℤ one-ℤ (inr (inl star))) (mul-ℤ neg-one-ℤ (inl y)) ＝ gcd-ℤ (inr (inl star)) (inl y)
  eqn = equational-reasoning
    add-ℤ (mul-ℤ one-ℤ (inr (inl star))) (mul-ℤ neg-one-ℤ (inl y))
    ＝ add-ℤ (mul-ℤ one-ℤ (inr (inl star))) (inr (inr y))
    by ap (λ M → add-ℤ (mul-ℤ one-ℤ (inr (inl star))) M) (inv (is-mul-neg-one-neg-ℤ (inl y)))
    ＝ add-ℤ zero-ℤ (inr (inr y)) by ap (λ M → add-ℤ M (inr (inr y))) (right-zero-law-mul-ℤ one-ℤ)
    ＝ int-ℕ (abs-ℤ (inl y)) by left-unit-law-add-ℤ (inr (inr y))
    ＝ gcd-ℤ zero-ℤ (inl y) by inv (is-id-is-gcd-zero-ℤ {inl y} {gcd-ℤ zero-ℤ (inl y)} refl)
bezouts-lemma-ℤ (inr (inl star)) (inr (inl star)) = pair one-ℤ (pair one-ℤ eqn)
  where
  eqn : add-ℤ (mul-ℤ one-ℤ (inr (inl star))) (mul-ℤ one-ℤ (inr (inl star))) ＝ gcd-ℤ zero-ℤ zero-ℤ
  eqn = equational-reasoning
    add-ℤ (mul-ℤ one-ℤ (inr (inl star))) (mul-ℤ one-ℤ (inr (inl star)))
    ＝ add-ℤ zero-ℤ (mul-ℤ one-ℤ (inr (inl star))) by ap (λ M → add-ℤ M (mul-ℤ one-ℤ (inr (inl star)))) (right-zero-law-mul-ℤ one-ℤ)
    ＝ add-ℤ zero-ℤ zero-ℤ by ap (λ M → add-ℤ zero-ℤ M) (right-zero-law-mul-ℤ one-ℤ)
    ＝ gcd-ℤ zero-ℤ zero-ℤ by inv (is-zero-gcd-ℤ zero-ℤ zero-ℤ refl refl)
bezouts-lemma-ℤ (inr (inl star)) (inr (inr y)) = pair one-ℤ (pair one-ℤ eqn)
  where
  eqn : add-ℤ (mul-ℤ one-ℤ (inr (inl star))) (mul-ℤ one-ℤ (inr (inr y))) ＝ gcd-ℤ (inr (inl star)) (inr (inr y))
  eqn = equational-reasoning
    add-ℤ (mul-ℤ one-ℤ (inr (inl star))) (mul-ℤ one-ℤ (inr (inr y)))
    ＝ add-ℤ (mul-ℤ one-ℤ (inr (inl star))) (inr (inr y))
    by ap (λ M → add-ℤ (mul-ℤ one-ℤ (inr (inl star))) M) (inv (left-unit-law-mul-ℤ (inr (inr y))))
    ＝ add-ℤ zero-ℤ (inr (inr y)) by ap (λ M → add-ℤ M (inr (inr y))) (right-zero-law-mul-ℤ one-ℤ)
    ＝ int-ℕ (abs-ℤ (inr (inr y))) by left-unit-law-add-ℤ (inr (inr y))
    ＝ gcd-ℤ zero-ℤ (inr (inr y)) by inv (is-id-is-gcd-zero-ℤ {inr (inr y)} {gcd-ℤ zero-ℤ (inr (inr y))} refl)
bezouts-lemma-ℤ (inr (inr x)) (inl y) = pair s (pair (neg-ℤ t) eqn)
  where 
  pos-bezout : Σ ℤ (λ s → Σ ℤ (λ t → add-ℤ (mul-ℤ s (inr (inr x))) (mul-ℤ t (inr (inr y))) ＝ gcd-ℤ (inr (inr x)) (inr (inr y))))
  pos-bezout = bezouts-lemma-pos-ints (inr (inr x)) (inr (inr y)) star star
  s : ℤ 
  s = pr1 (pos-bezout)
  t : ℤ 
  t = pr1 (pr2 (pos-bezout))
  eqn : add-ℤ (mul-ℤ s (inr (inr x))) (mul-ℤ (neg-ℤ t) (inl y)) ＝ gcd-ℤ (inr (inr x)) (inl y)
  eqn = equational-reasoning
    add-ℤ (mul-ℤ s (inr (inr x))) (mul-ℤ (neg-ℤ t) (neg-ℤ (inr (inr y))))
    ＝ add-ℤ (mul-ℤ s (inr (inr x))) (mul-ℤ t (inr (inr y)))
    by ap (λ M → add-ℤ (mul-ℤ s (inr (inr x))) M)
      (double-negative-law-mul-ℤ t (inr (inr y)))
    ＝ gcd-ℤ (inr (inr x)) (inr (inr y)) by pr2 (pr2 (pos-bezout))
    ＝ gcd-ℤ (inr (inr x)) (inl y) by ap (λ M → (int-ℕ (gcd-ℕ (succ-ℕ x) M))) (abs-neg-ℤ (inr (inr y))) 
bezouts-lemma-ℤ (inr (inr x)) (inr (inl star)) = pair one-ℤ (pair one-ℤ eqn)
  where
  eqn : add-ℤ (mul-ℤ one-ℤ (inr (inr x))) (mul-ℤ one-ℤ (inr (inl star))) ＝ gcd-ℤ (inr (inr x)) (inr (inl star))
  eqn = equational-reasoning
    add-ℤ (mul-ℤ one-ℤ (inr (inr x))) (mul-ℤ one-ℤ (inr (inl star)))
    ＝ add-ℤ (inr (inr x)) (mul-ℤ one-ℤ (inr (inl star)))
    by ap (λ M → add-ℤ M (mul-ℤ one-ℤ (inr (inl star)))) (left-unit-law-mul-ℤ (inr (inr x)))
    ＝ add-ℤ (inr (inr x)) zero-ℤ by ap (λ M → add-ℤ (inr (inr x)) M) (right-zero-law-mul-ℤ one-ℤ)
    ＝ int-ℕ (abs-ℤ (inr (inr x))) by right-unit-law-add-ℤ (inr (inr x))
    ＝ gcd-ℤ (inr (inr x)) zero-ℤ by inv (is-id-is-gcd-zero-ℤ' {inr (inr x)} {gcd-ℤ (inr (inr x)) zero-ℤ} refl)
bezouts-lemma-ℤ (inr (inr x)) (inr (inr y)) = bezouts-lemma-pos-ints (inr (inr x)) (inr (inr y)) star star 
```

Now that Bezout's Lemma has been established, we establish a few corollaries of Bezout. 

### If `x | y z` and `gcd-Z x y ＝ 1`, then `x | z`. 
```agda
div-right-factor-coprime-ℤ : (x y z : ℤ) → (div-ℤ x (mul-ℤ y z)) → (gcd-ℤ x y ＝ one-ℤ) → div-ℤ x z
div-right-factor-coprime-ℤ x y z H K = pair (add-ℤ (mul-ℤ s z) (mul-ℤ t k)) eqn 
  where
  bezout-triple : Σ ℤ (λ s → Σ ℤ (λ t → add-ℤ (mul-ℤ s x) (mul-ℤ t y) ＝ gcd-ℤ x y))
  bezout-triple = bezouts-lemma-ℤ x y
  s : ℤ
  s = pr1 bezout-triple
  t : ℤ
  t = pr1 (pr2 bezout-triple)
  bezout-eqn : add-ℤ (mul-ℤ s x) (mul-ℤ t y) ＝ gcd-ℤ x y
  bezout-eqn = pr2 (pr2 bezout-triple)
  k : ℤ
  k = pr1 H
  div-yz : mul-ℤ k x ＝ mul-ℤ y z
  div-yz = pr2 H 
  eqn : mul-ℤ (add-ℤ (mul-ℤ s z) (mul-ℤ t k)) x ＝ z
  eqn = equational-reasoning 
    mul-ℤ (add-ℤ (mul-ℤ s z) (mul-ℤ t k)) x
    ＝ add-ℤ (mul-ℤ (mul-ℤ s z) x) (mul-ℤ (mul-ℤ t k) x) by right-distributive-mul-add-ℤ (mul-ℤ s z) (mul-ℤ t k) x
    ＝ add-ℤ (mul-ℤ (mul-ℤ s x) z) (mul-ℤ (mul-ℤ t k) x) by ap (λ M → add-ℤ M (mul-ℤ (mul-ℤ t k) x))
      (equational-reasoning
        mul-ℤ (mul-ℤ s z) x
        ＝ mul-ℤ s (mul-ℤ z x) by associative-mul-ℤ s z x
        ＝ mul-ℤ s (mul-ℤ x z) by ap (λ P → mul-ℤ s P) (commutative-mul-ℤ z x)
        ＝ mul-ℤ (mul-ℤ s x) z by inv (associative-mul-ℤ s x z))
    ＝ add-ℤ (mul-ℤ (mul-ℤ s x) z) (mul-ℤ (mul-ℤ t y) z) by ap (λ M → add-ℤ (mul-ℤ (mul-ℤ s x) z) M) 
    (equational-reasoning
      mul-ℤ (mul-ℤ t k) x
      ＝ mul-ℤ t (mul-ℤ k x) by associative-mul-ℤ t k x
      ＝ mul-ℤ t (mul-ℤ y z) by ap (λ P → mul-ℤ t P) div-yz
      ＝ mul-ℤ (mul-ℤ t y) z by inv (associative-mul-ℤ t y z)) 
    ＝ mul-ℤ (add-ℤ (mul-ℤ s x) (mul-ℤ t y)) z by inv (right-distributive-mul-add-ℤ (mul-ℤ s x) (mul-ℤ t y) z)
    ＝ mul-ℤ one-ℤ z by ap (λ M → mul-ℤ M z) (bezout-eqn ∙ K)
    ＝ z by left-unit-law-mul-ℤ z
```

