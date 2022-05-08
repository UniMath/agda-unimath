---
title: Iterating functions
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.iterating-functions where

open import elementary-number-theory.addition-natural-numbers using
  ( add-ℕ; commutative-add-ℕ; left-unit-law-add-ℕ; right-unit-law-add-ℕ;
    ℕ-Monoid)
open import
  elementary-number-theory.modular-arithmetic-standard-finite-types using
  ( mod-two-ℕ)
open import elementary-number-theory.natural-numbers using (ℕ; zero-ℕ; succ-ℕ)

open import foundation.automorphisms using (Aut)
open import foundation.coproduct-types using (inl; inr)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using
  ( _∘e_; id-equiv; map-equiv; is-equiv-map-equiv; is-equiv)
open import foundation.homotopies using (_~_; refl-htpy; _·l_)
open import foundation.identity-types using
  ( Id; refl; _∙_; inv; ap; right-unit; ap-comp)
open import foundation.involutions using (is-involution)
open import foundation.unit-type using (star)
open import foundation.universe-levels using (Level; UU)

open import group-theory.monoid-actions using (Monoid-Action)

open import univalent-combinatorics.standard-finite-types using (nat-Fin; Fin; succ-Fin)
```

## Idea

Any map `f : X → X` can be iterated by repeatedly applying `f`

## Definition

```agda
module _
  {l : Level} {X : UU l}
  where
  
  iterate : ℕ → (X → X) → (X → X)
  iterate zero-ℕ f x = x
  iterate (succ-ℕ k) f x = f (iterate k f x)

  iterate' : ℕ → (X → X) → (X → X)
  iterate' zero-ℕ f x = x
  iterate' (succ-ℕ k) f x = iterate' k f (f x)
```

## Properties

### The two definitions of iterating are homotopic

```agda
module _
  {l : Level} {X : UU l}
  where

  iterate-succ-ℕ :
    (k : ℕ) (f : X → X) (x : X) →
    Id (iterate (succ-ℕ k) f x) (iterate k f (f x))
  iterate-succ-ℕ zero-ℕ f x = refl
  iterate-succ-ℕ (succ-ℕ k) f x = ap f (iterate-succ-ℕ k f x)

  reassociate-iterate : (k : ℕ) (f : X → X) → iterate k f ~ iterate' k f
  reassociate-iterate zero-ℕ f x = refl
  reassociate-iterate (succ-ℕ k) f x =
    iterate-succ-ℕ k f x ∙ reassociate-iterate k f (f x)
```

### For any map `f : X → X`, iterating `f` defines a monoid action of ℕ on `X`

```agda
module _
  {l : Level} {X : UU l}
  where

  iterate-add-ℕ :
    (k l : ℕ) (f : X → X) (x : X) →
    Id (iterate (add-ℕ k l) f x) (iterate k f (iterate l f x))
  iterate-add-ℕ k zero-ℕ f x = refl
  iterate-add-ℕ k (succ-ℕ l) f x =
    ap f (iterate-add-ℕ k l f x) ∙ iterate-succ-ℕ k f (iterate l f x)

  left-unit-law-iterate-add-ℕ :
    (l : ℕ) (f : X → X) (x : X) →
    Id ( iterate-add-ℕ 0 l f x)
       ( ap (λ t → iterate t f x) (left-unit-law-add-ℕ l))
  left-unit-law-iterate-add-ℕ zero-ℕ f x = refl
  left-unit-law-iterate-add-ℕ (succ-ℕ l) f x =
    ( right-unit) ∙
    ( ( ap (ap f) (left-unit-law-iterate-add-ℕ l f x)) ∙
      ( ( inv (ap-comp f (λ t → iterate t f x) (left-unit-law-add-ℕ l))) ∙
        ( ap-comp (λ t → iterate t f x) succ-ℕ (left-unit-law-add-ℕ l))))

  right-unit-law-iterate-add-ℕ :
    (k : ℕ) (f : X → X) (x : X) →
    Id ( iterate-add-ℕ k 0 f x)
       ( ap (λ t → iterate t f x) (right-unit-law-add-ℕ k))
  right-unit-law-iterate-add-ℕ k f x = refl

  iterative-Monoid-Action : (X → X) → Monoid-Action ℕ-Monoid l
  pr1 (iterative-Monoid-Action f) = X
  pr2 (iterative-Monoid-Action f) k x = iterate k f x
```

### Iterating `f` first `k` and then `l` times is the same as iterating `f` first `l` and then `k` times

```agda
  iterate-iterate :
    (k l : ℕ) (f : X → X) (x : X) →
    Id (iterate k f (iterate l f x)) (iterate l f (iterate k f x))
  iterate-iterate k l f x =
    ( inv (iterate-add-ℕ k l f x)) ∙
    ( ( ap (λ t → iterate t f x) (commutative-add-ℕ k l)) ∙
      ( iterate-add-ℕ l k f x))
```
