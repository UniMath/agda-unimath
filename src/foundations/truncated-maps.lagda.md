---
title: Univalent Mathematics in Agda
---

# Truncated maps

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundations.truncated-maps where

open import foundations.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundations.equality-fibers-of-maps using
  ( equiv-fib-ap-eq-fib; eq-fib-fib-ap; is-equiv-eq-fib-fib-ap)
open import foundations.fibers-of-maps using
  ( fib; equiv-fib-pr1; inv-equiv-fib-pr1)
open import foundations.identity-types using (Id; refl; ap; _∙_; inv)
open import foundations.levels using (Level; UU; _⊔_)
open import foundations.propositional-maps using
  ( is-prop-map-is-emb; is-emb-is-prop-map)
open import foundations.sets using
  ( is-set; is-set-equiv; UU-Set; type-Set; is-set-type-Set)
open import foundations.truncated-types using
  ( is-trunc; is-trunc-succ-is-trunc; is-trunc-equiv; UU-Truncated-Type;
    is-trunc-is-equiv')
open import foundations.truncation-levels using
  ( 𝕋; neg-two-𝕋; neg-one-𝕋; succ-𝕋)
```

```agda
module _
  {l1 l2 : Level} (k : 𝕋)
  where

  is-trunc-map : {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
  is-trunc-map f = (y : _) → is-trunc k (fib f y)
  
  trunc-map : (A : UU l1) (B : UU l2) → UU (l1 ⊔ l2)
  trunc-map A B = Σ (A → B) is-trunc-map

module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : UU l2}
  where

  map-trunc-map : trunc-map k A B → A → B
  map-trunc-map = pr1

  abstract
    is-trunc-map-map-trunc-map :
      (f : trunc-map k A B) → is-trunc-map k (map-trunc-map f)
    is-trunc-map-map-trunc-map = pr2

module _
  {l1 l2 : Level}
  where

  is-0-map : {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
  is-0-map {A} {B} f = (y : B) → is-set (fib f y)

  0-map : (A : UU l1) (B : UU l2) → UU (l1 ⊔ l2)
  0-map A B = Σ (A → B) is-0-map

  map-0-map : {A : UU l1} {B : UU l2} → 0-map A B → A → B
  map-0-map = pr1

  is-0-map-map-0-map :
    {A : UU l1} {B : UU l2} (f : 0-map A B) → is-0-map (map-0-map f)
  is-0-map-map-0-map = pr2
```

## If a map is k-truncated, then it is (k+1)-truncated

```agda
abstract
  is-trunc-map-succ-is-trunc-map :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2}
    (f : A → B) → is-trunc-map k f → is-trunc-map (succ-𝕋 k) f
  is-trunc-map-succ-is-trunc-map k f is-trunc-f b =
    is-trunc-succ-is-trunc k (is-trunc-f b)
```

```agda
module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B)
  where
  
  abstract
    is-trunc-map-is-trunc-map-ap :
      ((x y : A) → is-trunc-map k (ap f {x} {y})) → is-trunc-map (succ-𝕋 k) f
    is-trunc-map-is-trunc-map-ap is-trunc-map-ap-f b (pair x p) (pair x' p') =
      is-trunc-equiv k
        ( fib (ap f) (p ∙ (inv p')))
        ( equiv-fib-ap-eq-fib f (pair x p) (pair x' p'))
        ( is-trunc-map-ap-f x x' (p ∙ (inv p')))      

  abstract
    is-trunc-map-ap-is-trunc-map :
      is-trunc-map (succ-𝕋 k) f → (x y : A) → is-trunc-map k (ap f {x} {y})
    is-trunc-map-ap-is-trunc-map is-trunc-map-f x y p =
      is-trunc-is-equiv' k
        ( Id (pair x p) (pair y refl))
        ( eq-fib-fib-ap f x y p)
        ( is-equiv-eq-fib-fib-ap f x y p)
        ( is-trunc-map-f (f y) (pair x p) (pair y refl))

module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1}
  where

  abstract
    is-trunc-map-pr1 :
      {B : A → UU l2} → ((x : A) → is-trunc k (B x)) →
      is-trunc-map k (pr1 {l1} {l2} {A} {B})
    is-trunc-map-pr1 {B} H x =
      is-trunc-equiv k (B x) (equiv-fib-pr1 B x) (H x)

  pr1-trunc-map :
    (B : A → UU-Truncated-Type k l2) → trunc-map k (Σ A (λ x → pr1 (B x))) A
  pr1 (pr1-trunc-map B) = pr1
  pr2 (pr1-trunc-map B) = is-trunc-map-pr1 (λ x → pr2 (B x))

  abstract
    is-trunc-is-trunc-map-pr1 :
      (B : A → UU l2) → is-trunc-map k (pr1 {l1} {l2} {A} {B}) →
      ((x : A) → is-trunc k (B x))
    is-trunc-is-trunc-map-pr1 B is-trunc-map-pr1 x =
      is-trunc-equiv k (fib pr1 x) (inv-equiv-fib-pr1 B x) (is-trunc-map-pr1 x)
```

```agda
module _
  {l1 l2 : Level} {A : UU l1}
  where
  
  abstract
    is-0-map-pr1 :
      {B : A → UU l2} → ((x : A) → is-set (B x)) → is-0-map (pr1 {B = B})
    is-0-map-pr1 {B} H x =
      is-set-equiv (B x) (equiv-fib-pr1 B x) (H x)
                                                  
  pr1-0-map :
    (B : A → UU-Set l2) → 0-map (Σ A (λ x → type-Set (B x))) A
  pr1 (pr1-0-map B) = pr1
  pr2 (pr1-0-map B) = is-0-map-pr1 (λ x → is-set-type-Set (B x))
```
