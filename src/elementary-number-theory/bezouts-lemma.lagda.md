---
title: Bezout's lemma
---

```agda
module elementary-number-theory.bezouts-lemma where

open import elementary-number-theory.distance-natural-numbers
open import elementary-number-theory.divisibility-modular-arithmetic
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.modular-arithmetic
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.well-ordering-principle-natural-numbers

open import elementary-number-theory.integers
open import elementary-number-theory.addition-integers
open import elementary-number-theory.multiplication-integers 
open import elementary-number-theory.congruence-integers
open import elementary-number-theory.distance-integers
open import elementary-number-theory.absolute-value-integers

open import univalent-combinatorics.standard-finite-types

open import foundation.decidable-maps
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels
open import foundation.negation
open import foundation.coproduct-types
open import foundation.cartesian-product-types
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
```

## Lemmas

### If `z = dist-ℕ (kx, ly)` for some `k` and `l`, then `[y] | [z]` in `ℤ-Mod x`

If `z = dist-ℕ (kx, ly)` for some `k` and `l`, then it follows that `ly ≡ ±z mod x`. It follows that `±ly ≡ z mod x`, and therefore that `[y] | [z]` in `ℤ-Mod x`

```agda
div-mod-is-distance-between-multiples-ℕ :
  (x y z : ℕ) →
  is-distance-between-multiples-ℕ x y z → div-ℤ-Mod x (mod-ℕ x y) (mod-ℕ x z)
div-mod-is-distance-between-multiples-ℕ x y z (k , l , p) 
  with decide-leq-ℕ (mul-ℕ k x) (mul-ℕ l y)
... | inl kxly = (mod-ℕ x l , inv (path))
  where   
  add-dist : int-ℕ (add-ℕ z (mul-ℕ k x)) ＝ int-ℕ (mul-ℕ l y)
  add-dist = ap (int-ℕ) 
    ( rewrite-left-dist-add-ℕ z (mul-ℕ k x) (mul-ℕ l y) kxly (inv p))

  unfold-mods : mod-ℤ x (add-ℤ (int-ℕ z) (mul-ℤ (int-ℕ k) (int-ℕ x))) ＝ 
    mod-ℤ x (mul-ℤ (int-ℕ l) (int-ℕ y))
  unfold-mods = ap (mod-ℤ x) 
    ( ap (λ p → add-ℤ (int-ℕ z) p) (mul-int-ℕ k x) 
    ∙ ( add-int-ℕ z (mul-ℕ k x) 
    ∙ ( add-dist 
    ∙ ( inv (mul-int-ℕ l y)))))

  path : mod-ℕ x z ＝ mul-ℤ-Mod x (mod-ℕ x l) (mod-ℕ x y)
  path = inv (mod-int-ℕ x z) 
    ∙ ( ap (mod-ℤ x) (inv (right-unit-law-add-ℤ (int-ℕ z)))
    ∙ ( preserves-add-mod-ℤ x (int-ℕ z) zero-ℤ 
    ∙ ( ap (λ p → add-ℤ-Mod x (mod-ℤ x (int-ℕ z)) (mod-ℤ x p)) 
      (inv (right-zero-law-mul-ℤ (int-ℕ k))) 
    ∙ ( ap (λ p → add-ℤ-Mod x (mod-ℤ x (int-ℕ z)) p) 
      (preserves-mul-mod-ℤ x (int-ℕ k) zero-ℤ)
    ∙ ( ap (λ p → 
        add-ℤ-Mod x (mod-ℤ x (int-ℕ z)) (mul-ℤ-Mod x (mod-ℤ x (int-ℕ k)) p))
      (mod-zero-ℤ x)   
    ∙ ( ap (λ p → 
         add-ℤ-Mod x (mod-ℤ x (int-ℕ z)) (mul-ℤ-Mod x (mod-ℤ x (int-ℕ k)) p)) 
      (inv (mod-refl-ℕ x))  
    ∙ ( ap (λ p → 
         add-ℤ-Mod x (mod-ℤ x (int-ℕ z)) (mul-ℤ-Mod x (mod-ℤ x (int-ℕ k)) p)) 
      (inv (mod-int-ℕ x x))  
    ∙ ( ap (λ p → add-ℤ-Mod x (mod-ℤ x (int-ℕ z)) p)
      (inv (preserves-mul-mod-ℤ x (int-ℕ k) (int-ℕ x))) 
    ∙ ( inv (preserves-add-mod-ℤ x (int-ℕ z) (mul-ℤ (int-ℕ k) (int-ℕ x))) 
    ∙ ( unfold-mods
    ∙ ( preserves-mul-mod-ℤ x (int-ℕ l) (int-ℕ y) 
    ∙ ( ap (λ p → mul-ℤ-Mod x (mod-ℤ x (int-ℕ l)) p) (mod-int-ℕ x y) 
    ∙ ( ap (λ p → mul-ℤ-Mod x p (mod-ℕ x y)) (mod-int-ℕ x l) )))))))))))))  
... | inr lykx = (mod-ℤ x (neg-ℤ (int-ℕ l)) , inv path)
  where
  add-dist : int-ℕ (add-ℕ (mul-ℕ l y) z) ＝ int-ℕ (mul-ℕ k x)
  add-dist = ap (int-ℕ) 
    ( rewrite-right-dist-add-ℕ (mul-ℕ l y) z (mul-ℕ k x) lykx 
    (inv p ∙ symmetric-dist-ℕ (mul-ℕ k x) (mul-ℕ l y)) )

  unfold-ints : add-ℤ (mul-ℤ (int-ℕ l) (int-ℕ y)) (int-ℕ z) ＝ 
    mul-ℤ (int-ℕ k) (int-ℕ x)
  unfold-ints = ap (λ p → add-ℤ p (int-ℕ z)) (mul-int-ℕ l y) 
    ∙ ( add-int-ℕ (mul-ℕ l y) z 
    ∙ ( add-dist 
    ∙ ( inv (mul-int-ℕ k x))))

  rearrange : mod-ℤ x (int-ℕ z) ＝ 
    mod-ℤ x ( add-ℤ (mul-ℤ (neg-ℤ (int-ℕ l)) (int-ℕ y)) 
      (mul-ℤ (int-ℕ k) (int-ℕ x)))
  rearrange = ap (mod-ℤ x) 
    (inv (isretr-add-neg-ℤ (mul-ℤ (int-ℕ l) (int-ℕ y)) (int-ℕ z))
    ∙ ( ap (add-ℤ (neg-ℤ (mul-ℤ (int-ℕ l) (int-ℕ y)))) unfold-ints 
    ∙ ( ap (λ p → add-ℤ p (mul-ℤ (int-ℕ k) (int-ℕ x))) 
      (inv (left-negative-law-mul-ℤ (int-ℕ l) (int-ℕ y))))))
  
  path : mod-ℕ x z ＝ mul-ℤ-Mod x (mod-ℤ x (neg-ℤ (int-ℕ l))) (mod-ℕ x y)
  path = inv (mod-int-ℕ x z) 
    ∙ ( rearrange 
    ∙ ( preserves-add-mod-ℤ x (mul-ℤ (neg-ℤ (int-ℕ l)) (int-ℕ y)) 
      (mul-ℤ (int-ℕ k) (int-ℕ x)) 
    ∙ ( ap (λ p → add-ℤ-Mod x (mod-ℤ x (mul-ℤ (neg-ℤ (int-ℕ l)) (int-ℕ y))) p) 
      (preserves-mul-mod-ℤ x (int-ℕ k) (int-ℕ x)) 
    ∙ ( ap (λ p → add-ℤ-Mod x 
            (mod-ℤ x (mul-ℤ (neg-ℤ (int-ℕ l)) (int-ℕ y))) 
            (mul-ℤ-Mod x (mod-ℤ x (int-ℕ k)) p)) 
        (mod-int-ℕ x x ∙ (mod-refl-ℕ x ∙ inv (mod-zero-ℤ x))) 
    ∙ ( ap (λ p → add-ℤ-Mod x (mod-ℤ x (mul-ℤ (neg-ℤ (int-ℕ l)) (int-ℕ y))) p)
      (inv (preserves-mul-mod-ℤ x (int-ℕ k) zero-ℤ)) 
    ∙ ( ap (λ p → add-ℤ-Mod x 
             (mod-ℤ x (mul-ℤ (neg-ℤ (int-ℕ l)) (int-ℕ y))) (mod-ℤ x p)) 
      (right-zero-law-mul-ℤ (int-ℕ k)) 
    ∙ ( inv (preserves-add-mod-ℤ x (mul-ℤ (neg-ℤ (int-ℕ l)) (int-ℕ y)) (zero-ℤ)) 
    ∙ ( ap (mod-ℤ x) (right-unit-law-add-ℤ (mul-ℤ (neg-ℤ (int-ℕ l)) (int-ℕ y)))
    ∙ ( preserves-mul-mod-ℤ x (neg-ℤ (int-ℕ l)) (int-ℕ y) 
    ∙ ( ap (λ p → mul-ℤ-Mod x (mod-ℤ x (neg-ℤ (int-ℕ l))) p) 
      (mod-int-ℕ x y)))))))))))
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

Since `is-distance-between-multiples-ℕ x y z` is decidable, we can prove Bezout's lemma by the well-ordering principle: take the least positive distance `d` between multiples of `x` and `y`. Then `d` divides both `x` and `y`. Since `gcd x y` divides any number of the form `dist-ℕ (kx,ly)`, it follows that `gcd x y | d`, and hence that `gcd x y ＝ d`.

```agda
pos-distance-between-multiples : (x y z : ℕ) → UU lzero
pos-distance-between-multiples x y z = is-nonzero-ℕ (add-ℕ x y) → (is-nonzero-ℕ z) × (is-distance-between-multiples-ℕ x y z)   
  
minimal-pos-distance-between-multiples : (x y : ℕ) → minimal-element-ℕ (pos-distance-between-multiples x y)
minimal-pos-distance-between-multiples zero-ℕ zero-ℕ = {! !}
minimal-pos-distance-between-multiples zero-ℕ (succ-ℕ y) = {! !}
minimal-pos-distance-between-multiples (succ-ℕ x) zero-ℕ = {! !}
minimal-pos-distance-between-multiples (succ-ℕ x) (succ-ℕ y) = {! !}
-- well-ordering-principle-ℕ 
--  (pos-distance-between-multiples x y)
--  (λ z → is-decidable-prod (is-decidable-neg (is-decidable-is-zero-ℕ z)) (is-decidable-is-distance-between-multiples-ℕ x y z)) 
--  (pair x ? )

  

```
