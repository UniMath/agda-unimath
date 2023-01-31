# Vectors

```agda
{-# OPTIONS --without-K --exact-split #-}

module linear-algebra.vectors where

open import elementary-number-theory.natural-numbers

open import foundation.sets
open import foundation.identity-types
open import foundation.dependent-pair-types
open import foundation.universe-levels
```
## Idea

An vector of elements of type `A` of length `n` is a list of `n` elements of type `A`.

## Definition

```agda
infixr 5 _∷_

data vec {l : Level} (A : UU l) : ℕ → UU l where
  empty-vec : vec A zero-ℕ
  _∷_ : ∀ {n} → A → vec A n → vec A (succ-ℕ n)

head-vec : {l : Level} {A : UU l} {n : ℕ} → vec A (succ-ℕ n) → A
head-vec (x ∷ v) = x

tail-vec : {l : Level} {A : UU l} {n : ℕ} → vec A (succ-ℕ n) → vec A n
tail-vec (x ∷ v) = v
```

If `A` is a `k+2`-truncated type then vectors over `A` are also `k+2`-truncated.
In particular, vectors over a set form a set.

```agda

module _ {l : Level} (A : UU l) where
    open import foundation.unit-type
    open import foundation.raising-universe-levels
    open import foundation.cartesian-product-types
    open import foundation.sets
    open import foundation.equivalences
    open import foundation.truncated-types
    open import foundation.truncation-levels
    open import foundation.contractible-types
    
    Eq-vec : (n : ℕ) → vec A n → vec A n → UU l
    Eq-vec zero-ℕ empty-vec empty-vec = raise-unit l
    Eq-vec (succ-ℕ n) (x ∷ xs) (y ∷ ys) = (Id x y) × (Eq-vec n xs ys)

    refl-Eq-vec : (n : ℕ) → (u : vec A n) → Eq-vec n u u
    refl-Eq-vec zero-ℕ empty-vec = map-raise star
    refl-Eq-vec (succ-ℕ n) (x ∷ xs) = refl , refl-Eq-vec n xs

    Eq-eq-vec : (n : ℕ) → (u v : vec A n) → Id u v → Eq-vec n u v
    Eq-eq-vec n u .u refl = refl-Eq-vec n u

    eq-Eq-vec : (n : ℕ) → (u v : vec A n) → Eq-vec n u v → Id u v
    eq-Eq-vec zero-ℕ empty-vec empty-vec eq-vec = refl
    eq-Eq-vec (succ-ℕ n) (x ∷ xs) (.x ∷ ys) (refl , eqs) = ap (x ∷_) (eq-Eq-vec n xs ys eqs)

    left-inv-Eq-eq-vec : (n : ℕ) → (u v : vec A n) → (eq : Id u v) → Id (eq-Eq-vec n u v (Eq-eq-vec n u v eq)) eq
    left-inv-Eq-eq-vec zero-ℕ empty-vec empty-vec refl = refl
    left-inv-Eq-eq-vec (succ-ℕ n) (x ∷ xs) .(x ∷ xs) refl = ap (ap (x ∷_)) (left-inv-Eq-eq-vec n xs xs refl)

    square-Eq-eq-vec : (n : ℕ) (x : A) (u v : vec A n) (p : Id u v) →
        Id (Eq-eq-vec _ (x ∷ u) (x ∷ v) (ap (x ∷_) p)) (refl , (Eq-eq-vec n u v p))
    square-Eq-eq-vec zero-ℕ x empty-vec empty-vec refl = refl
    square-Eq-eq-vec (succ-ℕ n) a (x ∷ xs) (.x ∷ .xs) refl = refl

    right-inv-Eq-eq-vec : (n : ℕ) → (u v : vec A n) → (Eq : Eq-vec n u v) → Id (Eq-eq-vec n u v (eq-Eq-vec n u v Eq)) Eq
    right-inv-Eq-eq-vec zero-ℕ empty-vec empty-vec (map-raise star) = refl
    right-inv-Eq-eq-vec (succ-ℕ n) (x ∷ xs) (.x ∷ ys) (refl , eqs)
        = (square-Eq-eq-vec n x xs ys (eq-Eq-vec n xs ys eqs)) ∙ (ap (refl ,_) (right-inv-Eq-eq-vec n xs ys eqs))

    is-equiv-Eq-eq-vec : (n : ℕ) → (u v : vec A n) → is-equiv (Eq-eq-vec n u v)
    is-equiv-Eq-eq-vec n u v = is-equiv-has-inverse (eq-Eq-vec n u v) (right-inv-Eq-eq-vec n u v) (left-inv-Eq-eq-vec n u v)

    equiv-Eq-vec : (n : ℕ) → (u v : vec A n) → Id u v ≃ Eq-vec n u v
    equiv-Eq-vec n u v =  (Eq-eq-vec n u v , is-equiv-Eq-eq-vec n u v)

    is-trunc-Eq-vec : (n : ℕ) (k : 𝕋) → is-trunc (succ-𝕋 (succ-𝕋 k)) A → (u v : vec A n) 
        → is-trunc (succ-𝕋 k) (Eq-vec n u v)
    is-trunc-Eq-vec zero-ℕ k A-trunc empty-vec empty-vec = is-trunc-is-contr (succ-𝕋 k) is-contr-raise-unit
    is-trunc-Eq-vec (succ-ℕ n) k A-trunc (x ∷ xs) (y ∷ ys) = is-trunc-prod (succ-𝕋 k) (A-trunc x y) (is-trunc-Eq-vec n k A-trunc xs ys)

    is-trunc-vec : (n : ℕ) → (k : 𝕋) → is-trunc (succ-𝕋 (succ-𝕋 k)) A 
        → is-trunc (succ-𝕋 (succ-𝕋 k)) (vec A n)
    is-trunc-vec n k A-trunc u v = is-trunc-equiv (succ-𝕋 k) (Eq-vec n u v) (equiv-Eq-vec n u v) (is-trunc-Eq-vec n k A-trunc u v)

    is-set-vec : (n : ℕ) → is-set A -> is-set (vec A n)
    is-set-vec n = is-trunc-vec n (neg-two-𝕋)

vec-Set : {l : Level} → Set l → ℕ → Set l
vec-Set A n = vec (pr1 A) n , is-set-vec (pr1 A) n (pr2 A)

```