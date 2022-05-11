---
title: Univalent Mathematics in Agda
---

# Finitely cyclic maps

```agda
{-# OPTIONS --without-K --exact-split #-}

module elementary-number-theory.finitely-cyclic-maps where

open import
  elementary-number-theory.modular-arithmetic-standard-finite-types using
  ( add-Fin; mod-succ-ℕ; right-unit-law-add-Fin; right-successor-law-add-Fin;
    neg-Fin; issec-nat-Fin; commutative-add-Fin; associative-add-Fin;
    left-inverse-law-add-Fin)
open import elementary-number-theory.natural-numbers using (ℕ; zero-ℕ; succ-ℕ)

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using (is-equiv; is-equiv-has-inverse)
open import foundation.functions using (id; _∘_)
open import foundation.homotopies using (_~_)
open import foundation.identity-types using (Id; _∙_; inv; ap)
open import foundation.iterating-functions using
  ( iterate; iterate-succ-ℕ; iterate-iterate)
open import foundation.universe-levels using (Level; UU)

open import univalent-combinatorics.standard-finite-types using
  ( Fin; succ-Fin; nat-Fin)
```

# Finitely cyclic maps

```agda
module _
  {l : Level} {X : UU l}
  where

  is-finitely-cyclic-map : (f : X → X) → UU l
  is-finitely-cyclic-map f = (x y : X) → Σ ℕ (λ k → Id (iterate k f x) y)

  length-path-is-finitely-cyclic-map :
    {f : X → X} → is-finitely-cyclic-map f → X → X → ℕ
  length-path-is-finitely-cyclic-map H x y = pr1 (H x y)

  eq-is-finitely-cyclic-map :
    {f : X → X} (H : is-finitely-cyclic-map f) (x y : X) →
    Id (iterate (length-path-is-finitely-cyclic-map H x y) f x) y
  eq-is-finitely-cyclic-map H x y = pr2 (H x y)

  map-inv-is-finitely-cyclic-map :
    (f : X → X) (H : is-finitely-cyclic-map f) → X → X
  map-inv-is-finitely-cyclic-map f H x =
    iterate (length-path-is-finitely-cyclic-map H (f x) x) f x

  issec-map-inv-is-finitely-cyclic-map :
    (f : X → X) (H : is-finitely-cyclic-map f) →
    (f ∘ map-inv-is-finitely-cyclic-map f H) ~ id
  issec-map-inv-is-finitely-cyclic-map f H x =
    ( iterate-succ-ℕ (length-path-is-finitely-cyclic-map H (f x) x) f x) ∙
    ( eq-is-finitely-cyclic-map H (f x) x)

  isretr-map-inv-is-finitely-cyclic-map :
    (f : X → X) (H : is-finitely-cyclic-map f) →
    (map-inv-is-finitely-cyclic-map f H ∘ f) ~ id
  isretr-map-inv-is-finitely-cyclic-map f H x =
    ( ap ( iterate (length-path-is-finitely-cyclic-map H (f (f x)) (f x)) f ∘ f)
         ( inv (eq-is-finitely-cyclic-map H (f x) x))) ∙
    ( ( ap ( iterate (length-path-is-finitely-cyclic-map H (f (f x)) (f x)) f)
           ( iterate-succ-ℕ
             ( length-path-is-finitely-cyclic-map H (f x) x) f (f x))) ∙
      ( ( iterate-iterate
          ( length-path-is-finitely-cyclic-map H (f (f x)) (f x))
          ( length-path-is-finitely-cyclic-map H (f x) x) f (f (f x))) ∙
        ( ( ap ( iterate (length-path-is-finitely-cyclic-map H (f x) x) f)
            ( eq-is-finitely-cyclic-map H (f (f x)) (f x))) ∙
          ( eq-is-finitely-cyclic-map H (f x) x))))

  is-equiv-is-finitely-cyclic-map :
    (f : X → X) → is-finitely-cyclic-map f → is-equiv f
  is-equiv-is-finitely-cyclic-map f H =
    is-equiv-has-inverse
      ( map-inv-is-finitely-cyclic-map f H)
      ( issec-map-inv-is-finitely-cyclic-map f H)
      ( isretr-map-inv-is-finitely-cyclic-map f H)
```

# The successor functions on the standard finite types are finitely cyclic

```agda
compute-iterate-succ-Fin :
  {k : ℕ} (n : ℕ) (x : Fin (succ-ℕ k)) →
  Id (iterate n succ-Fin x) (add-Fin x (mod-succ-ℕ k n))
compute-iterate-succ-Fin zero-ℕ x = inv (right-unit-law-add-Fin x)
compute-iterate-succ-Fin {k} (succ-ℕ n) x =
  ( ap succ-Fin (compute-iterate-succ-Fin n x)) ∙
  ( inv (right-successor-law-add-Fin x (mod-succ-ℕ k n)))

is-finitely-cyclic-succ-Fin : {k : ℕ} → is-finitely-cyclic-map (succ-Fin {k})
pr1 (is-finitely-cyclic-succ-Fin {succ-ℕ k} x y) =
  nat-Fin (add-Fin y (neg-Fin x))
pr2 (is-finitely-cyclic-succ-Fin {succ-ℕ k} x y) =
  ( compute-iterate-succ-Fin (nat-Fin (add-Fin y (neg-Fin x))) x) ∙
    ( ( ap (add-Fin x) (issec-nat-Fin (add-Fin y (neg-Fin x)))) ∙
      ( ( commutative-add-Fin x (add-Fin y (neg-Fin x))) ∙
        ( ( associative-add-Fin y (neg-Fin x) x) ∙
          ( ( ap (add-Fin y) (left-inverse-law-add-Fin x)) ∙
            ( right-unit-law-add-Fin y)))))
```
