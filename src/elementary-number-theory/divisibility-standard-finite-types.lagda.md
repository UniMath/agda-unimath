# The divisibility relation on the standard finite types

```agda
{-# OPTIONS --without-K --exact-split #-}

module elementary-number-theory.divisibility-standard-finite-types where

open import elementary-number-theory.congruence-natural-numbers using
  ( cong-ℕ; concatenate-eq-cong-ℕ; scalar-invariant-cong-ℕ; symm-cong-ℕ)
open import elementary-number-theory.decidable-dependent-pair-types using
  ( is-decidable-Σ-Fin)
open import elementary-number-theory.distance-natural-numbers using
  ( right-unit-law-dist-ℕ)
open import
  elementary-number-theory.modular-arithmetic-standard-finite-types using
  ( mul-Fin; mul-Fin'; left-unit-law-mul-Fin; associative-mul-Fin;
    left-zero-law-mul-Fin; right-unit-law-mul-Fin; right-zero-law-mul-Fin;
    eq-mod-succ-cong-ℕ; commutative-mul-Fin; mod-succ-ℕ; cong-eq-mod-succ-ℕ;
    cong-nat-mod-succ-ℕ)
open import elementary-number-theory.multiplication-natural-numbers using
  ( mul-ℕ; square-succ-ℕ; commutative-mul-ℕ)
open import elementary-number-theory.natural-numbers using (ℕ; zero-ℕ; succ-ℕ)

open import foundation.decidable-types using (is-decidable)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.identity-types using (Id; _∙_; inv; ap)
open import foundation.universe-levels using (UU; lzero)

open import univalent-combinatorics.equality-standard-finite-types using
  ( has-decidable-equality-Fin)
open import univalent-combinatorics.standard-finite-types using
  ( Fin; zero-Fin; one-Fin; is-zero-Fin; neg-one-Fin; nat-Fin)
```

# Divisibility on the standard finite types

```agda
div-Fin : {k : ℕ} → Fin k → Fin k → UU lzero
div-Fin {k} x y = Σ (Fin k) (λ u → Id (mul-Fin u x) y)

refl-div-Fin : {k : ℕ} (x : Fin k) → div-Fin x x
pr1 (refl-div-Fin {succ-ℕ k} x) = one-Fin
pr2 (refl-div-Fin {succ-ℕ k} x) = left-unit-law-mul-Fin x

trans-div-Fin :
  {k : ℕ} (x y z : Fin k) → div-Fin x y → div-Fin y z → div-Fin x z
pr1 (trans-div-Fin x y z (pair u p) (pair v q)) = mul-Fin v u
pr2 (trans-div-Fin x y z (pair u p) (pair v q)) =
  associative-mul-Fin v u x ∙ (ap (mul-Fin v) p ∙ q)

div-zero-Fin : {k : ℕ} (x : Fin (succ-ℕ k)) → div-Fin x zero-Fin
pr1 (div-zero-Fin x) = zero-Fin
pr2 (div-zero-Fin x) = left-zero-law-mul-Fin x

div-one-Fin : {k : ℕ} (x : Fin (succ-ℕ k)) → div-Fin one-Fin x
pr1 (div-one-Fin x) = x
pr2 (div-one-Fin x) = right-unit-law-mul-Fin x

is-zero-div-zero-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → div-Fin zero-Fin x → is-zero-Fin x
is-zero-div-zero-Fin {k} x (pair u p) = inv p ∙ right-zero-law-mul-Fin u

is-unit-Fin : {k : ℕ} → Fin k → UU lzero
is-unit-Fin {succ-ℕ k} x = div-Fin x one-Fin

unit-Fin : ℕ → UU lzero
unit-Fin k = Σ (Fin k) is-unit-Fin

is-unit-one-Fin : {k : ℕ} → is-unit-Fin (one-Fin {k})
is-unit-one-Fin {k} = refl-div-Fin one-Fin

one-unit-Fin : {k : ℕ} → unit-Fin (succ-ℕ k)
pr1 (one-unit-Fin {k}) = one-Fin
pr2 (one-unit-Fin {k}) = is-unit-one-Fin

is-unit-neg-one-Fin : {k : ℕ} → is-unit-Fin (neg-one-Fin {k})
is-unit-neg-one-Fin {zero-ℕ} = refl-div-Fin neg-one-Fin
pr1 (is-unit-neg-one-Fin {succ-ℕ k}) = neg-one-Fin
pr2 (is-unit-neg-one-Fin {succ-ℕ k}) =
  eq-mod-succ-cong-ℕ
    ( succ-ℕ k)
    ( mul-ℕ (succ-ℕ k) (succ-ℕ k))
    ( 1)
    ( concatenate-eq-cong-ℕ
      ( succ-ℕ (succ-ℕ k))
      { x3 = 1}
      ( square-succ-ℕ k)
      ( pair k
        ( ( commutative-mul-ℕ k (succ-ℕ (succ-ℕ k))) ∙
          ( inv (right-unit-law-dist-ℕ (mul-ℕ (succ-ℕ (succ-ℕ k)) k))))))

neg-one-unit-Fin : {k : ℕ} → unit-Fin (succ-ℕ k)
pr1 neg-one-unit-Fin = neg-one-Fin
pr2 neg-one-unit-Fin = is-unit-neg-one-Fin

is-unit-mul-Fin :
  {k : ℕ} {x y : Fin k} →
  is-unit-Fin x → is-unit-Fin y → is-unit-Fin (mul-Fin x y)
pr1 (is-unit-mul-Fin {succ-ℕ k} {x} {y} (pair d p) (pair e q)) = mul-Fin e d
pr2 (is-unit-mul-Fin {succ-ℕ k} {x} {y} (pair d p) (pair e q)) =
  ( associative-mul-Fin e d (mul-Fin x y)) ∙
    ( ( ap
        ( mul-Fin e)
        ( ( inv (associative-mul-Fin d x y)) ∙
          ( ap (mul-Fin' y) p ∙ left-unit-law-mul-Fin y))) ∙
      ( q))

mul-unit-Fin : {k : ℕ} → unit-Fin k → unit-Fin k → unit-Fin k
pr1 (mul-unit-Fin u v) = mul-Fin (pr1 u) (pr1 v)
pr2 (mul-unit-Fin u v) = is-unit-mul-Fin (pr2 u) (pr2 v)

inv-unit-Fin : {k : ℕ} → unit-Fin k → unit-Fin k
pr1 (inv-unit-Fin {succ-ℕ k} (pair u (pair v p))) = v
pr1 (pr2 (inv-unit-Fin {succ-ℕ k} (pair u (pair v p)))) = u
pr2 (pr2 (inv-unit-Fin {succ-ℕ k} (pair u (pair v p)))) =
  commutative-mul-Fin u v ∙ p

sim-unit-Fin :
  {k : ℕ} → Fin k → Fin k → UU lzero
sim-unit-Fin {k} x y = Σ (unit-Fin k) (λ u → Id (mul-Fin (pr1 u) x) y)

refl-sim-unit-Fin :
  {k : ℕ} (x : Fin k) → sim-unit-Fin x x
pr1 (refl-sim-unit-Fin {succ-ℕ k} x) = one-unit-Fin
pr2 (refl-sim-unit-Fin {succ-ℕ k} x) = left-unit-law-mul-Fin x

symm-sim-unit-Fin :
  {k : ℕ} (x y : Fin k) → sim-unit-Fin x y → sim-unit-Fin y x
pr1 (symm-sim-unit-Fin {succ-ℕ k} x y (pair (pair u (pair v q)) p)) =
  inv-unit-Fin (pair u (pair v q))
pr2 (symm-sim-unit-Fin {succ-ℕ k} x y (pair (pair u (pair v q)) p)) =
  ( ( ( ap (mul-Fin v) (inv p)) ∙
        ( inv (associative-mul-Fin v u x))) ∙
      ( ap (mul-Fin' x) q)) ∙
    ( left-unit-law-mul-Fin x)

trans-sim-unit-Fin :
  {k : ℕ} (x y z : Fin k) → sim-unit-Fin x y → sim-unit-Fin y z →
  sim-unit-Fin x z
pr1 (trans-sim-unit-Fin {succ-ℕ k} x y z (pair u p) (pair v q)) =
  mul-unit-Fin v u
pr2 (trans-sim-unit-Fin {succ-ℕ k} x y z (pair u p) (pair v q)) =
  associative-mul-Fin (pr1 v) (pr1 u) x ∙ (ap (mul-Fin (pr1 v)) p ∙ q)

is-mod-unit-ℕ : (k x : ℕ) → UU lzero
is-mod-unit-ℕ k x = Σ ℕ (λ l → cong-ℕ k (mul-ℕ l x) 1)

is-mod-unit-sim-unit-mod-succ-ℕ :
  (k x : ℕ) → sim-unit-Fin (mod-succ-ℕ k x) one-Fin → is-mod-unit-ℕ (succ-ℕ k) x
pr1 (is-mod-unit-sim-unit-mod-succ-ℕ k x (pair u p)) =
  nat-Fin (pr1 u)
pr2 (is-mod-unit-sim-unit-mod-succ-ℕ k x (pair u p)) =
  cong-eq-mod-succ-ℕ k
    ( mul-ℕ (nat-Fin (pr1 u)) x)
    ( 1)
    ( ( eq-mod-succ-cong-ℕ k
        ( mul-ℕ (nat-Fin (pr1 u)) x)
        ( mul-ℕ (nat-Fin (pr1 u)) (nat-Fin (mod-succ-ℕ k x)))
        ( scalar-invariant-cong-ℕ
          ( succ-ℕ k)
          ( x)
          ( nat-Fin (mod-succ-ℕ k x))
          ( nat-Fin (pr1 u))
          ( symm-cong-ℕ
            ( succ-ℕ k)
            ( nat-Fin (mod-succ-ℕ k x))
            ( x)
            ( cong-nat-mod-succ-ℕ k x)))) ∙
      ( p))
```

```agda
is-decidable-div-Fin : {k : ℕ} (x y : Fin k) → is-decidable (div-Fin x y)
is-decidable-div-Fin x y =
  is-decidable-Σ-Fin (λ u → has-decidable-equality-Fin (mul-Fin u x) y)
```
