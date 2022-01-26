---
title: Univalent Mathematics in Agda
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundation.equality-fibers-of-maps where

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equality-dependent-pair-types using
  ( pair-eq-Σ; is-equiv-pair-eq-Σ)
open import foundation.equivalences using
  ( is-fiberwise-equiv; is-equiv-comp; is-equiv-concat; is-equiv-inv; is-equiv;
    is-equiv-tr; _≃_)
open import foundation.fibers-of-maps using (fib)
open import foundation.functions using (_∘_)
open import foundation.functoriality-dependent-pair-types using
  ( tot; is-equiv-tot-is-fiberwise-equiv)
open import foundation.homotopies using (refl-htpy; _~_)
open import foundation.identity-types using
  ( Id; tr; ap; _∙_; inv; concat; right-unit; right-inv; refl)
open import foundation.levels using (Level; UU)
```

# Equality in the fibers of a map

## Second characterization of equality in the fibers of a map

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) {b : B}
  where

  -- Characterizing the identity type of a fiber as the fiber of the action on
  -- paths

  fib-ap-eq-fib-fiberwise :
    (s t : fib f b) (p : Id (pr1 s) (pr1 t)) →
    (Id (tr (λ (a : A) → Id (f a) b) p (pr2 s)) (pr2 t)) →
    (Id (ap f p) ((pr2 s) ∙ (inv (pr2 t))))
  fib-ap-eq-fib-fiberwise (pair .x' p) (pair x' refl) refl =
    inv ∘ (concat right-unit refl)

  abstract
    is-fiberwise-equiv-fib-ap-eq-fib-fiberwise :
      (s t : fib f b) → is-fiberwise-equiv (fib-ap-eq-fib-fiberwise s t)
    is-fiberwise-equiv-fib-ap-eq-fib-fiberwise (pair x y) (pair .x refl) refl =
      is-equiv-comp
        ( fib-ap-eq-fib-fiberwise (pair x y) (pair x refl) refl)
        ( inv)
        ( concat right-unit refl)
        ( refl-htpy)
        ( is-equiv-concat right-unit refl)
        ( is-equiv-inv (y ∙ refl) refl)

  fib-ap-eq-fib :
    (s t : fib f b) → Id s t →
    fib (ap f {x = pr1 s} {y = pr1 t}) ((pr2 s) ∙ (inv (pr2 t)))
  pr1 (fib-ap-eq-fib s .s refl) = refl
  pr2 (fib-ap-eq-fib s .s refl) = inv (right-inv (pr2 s))

  triangle-fib-ap-eq-fib :
    (s t : fib f b) →
    ( fib-ap-eq-fib s t) ~
    ( (tot (fib-ap-eq-fib-fiberwise s t)) ∘ (pair-eq-Σ {s = s} {t}))
  triangle-fib-ap-eq-fib (pair x refl) .(pair x refl) refl = refl

  abstract
    is-equiv-fib-ap-eq-fib : (s t : fib f b) → is-equiv (fib-ap-eq-fib s t)
    is-equiv-fib-ap-eq-fib s t =
      is-equiv-comp
        ( fib-ap-eq-fib s t)
        ( tot (fib-ap-eq-fib-fiberwise s t))
        ( pair-eq-Σ {s = s} {t})
        ( triangle-fib-ap-eq-fib s t)
        ( is-equiv-pair-eq-Σ s t)
        ( is-equiv-tot-is-fiberwise-equiv
          ( is-fiberwise-equiv-fib-ap-eq-fib-fiberwise s t))

  equiv-fib-ap-eq-fib :
    (s t : fib f b) →
    Id s t ≃ fib (ap f {x = pr1 s} {y = pr1 t}) ((pr2 s) ∙ (inv (pr2 t)))
  pr1 (equiv-fib-ap-eq-fib s t) = fib-ap-eq-fib s t
  pr2 (equiv-fib-ap-eq-fib s t) = is-equiv-fib-ap-eq-fib s t

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (x y : A)
  where
  
  eq-fib-fib-ap :
    (q : Id (f x) (f y)) → Id (pair x q) (pair y refl) → fib (ap f {x} {y}) q
  eq-fib-fib-ap q =
    (tr (fib (ap f)) right-unit) ∘ (fib-ap-eq-fib f (pair x q) (pair y refl))

  abstract
    is-equiv-eq-fib-fib-ap :
      (q : Id (f x) (f y)) → is-equiv (eq-fib-fib-ap q)
    is-equiv-eq-fib-fib-ap q =
      is-equiv-comp
        ( eq-fib-fib-ap q)
        ( tr (fib (ap f)) right-unit)
        ( fib-ap-eq-fib f (pair x q) (pair y refl))
        ( refl-htpy)
        ( is-equiv-fib-ap-eq-fib f (pair x q) (pair y refl))
        ( is-equiv-tr (fib (ap f)) right-unit)
```
