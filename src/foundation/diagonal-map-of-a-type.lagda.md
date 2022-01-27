---
title: Univalent Mathematics in Agda
---

# The diagonal map of a type

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundation.diagonal-map-of-a-type where

open import foundation.1-types using
  ( is-1-type; UU-1-Type; type-1-Type; is-1-type-type-1-Type)
open import foundation.cartesian-product-types using (_×_)
open import foundation.contractible-maps using (is-contr-map)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.embeddings using (is-emb; _↪_)
open import foundation.equality-cartesian-product-types using (eq-pair)
open import foundation.equivalences using
  ( is-equiv; issec-map-inv-is-equiv; is-equiv-has-inverse)
open import foundation.faithful-maps using
  ( is-faithful; is-0-map-is-faithful; is-faithful-is-0-map; faithful-map)
open import foundation.fibers-of-maps using (fib)
open import foundation.functions using (_∘_; id)
open import foundation.homotopies using (_~_)
open import foundation.identity-types using (Id; refl; _∙_; inv; ap)
open import foundation.propositional-maps using
  ( is-prop-map; is-prop-map-is-emb; is-emb-is-prop-map)
open import foundation.propositions using
  ( is-prop; is-prop-all-elements-equal)
open import foundation.sets using (is-set; UU-Set; type-Set; is-set-type-Set)
open import foundation.truncated-maps using (is-trunc-map; is-0-map)
open import foundation.truncated-types using
  ( is-trunc; is-trunc-is-equiv'; is-trunc-is-equiv)
open import foundation.truncation-levels using
  ( 𝕋; neg-two-𝕋; neg-one-𝕋; zero-𝕋; succ-𝕋)
open import foundation.universe-levels using (Level; UU)
```

```agda
module _
  {l : Level} (A : UU l)
  where

  diagonal : A → A × A
  pr1 (diagonal x) = x
  pr2 (diagonal x) = x

  -- Exercise 12.4 (a)
  
  abstract
    is-prop-is-equiv-diagonal : is-equiv diagonal → is-prop A
    is-prop-is-equiv-diagonal is-equiv-d =
      is-prop-all-elements-equal ( λ x y →
        let α = issec-map-inv-is-equiv is-equiv-d (pair x y) in
        ( inv (ap pr1 α)) ∙ (ap pr2 α))
  
  eq-fib-diagonal : (t : A × A) → fib diagonal t → Id (pr1 t) (pr2 t)
  eq-fib-diagonal (pair x y) (pair z α) = (inv (ap pr1 α)) ∙ (ap pr2 α)
  
  fib-diagonal-eq : (t : A × A) → Id (pr1 t) (pr2 t) → fib diagonal t
  pr1 (fib-diagonal-eq (pair x y) β) = x
  pr2 (fib-diagonal-eq (pair x y) β) = eq-pair refl β
  
  issec-fib-diagonal-eq :
    (t : A × A) → ((eq-fib-diagonal t) ∘ (fib-diagonal-eq t)) ~ id
  issec-fib-diagonal-eq (pair x .x) refl = refl
  
  isretr-fib-diagonal-eq :
    (t : A × A) → ((fib-diagonal-eq t) ∘ (eq-fib-diagonal t)) ~ id
  isretr-fib-diagonal-eq .(pair z z) (pair z refl) = refl
  
  abstract
    is-equiv-eq-fib-diagonal : (t : A × A) → is-equiv (eq-fib-diagonal t)
    is-equiv-eq-fib-diagonal t =
      is-equiv-has-inverse
        ( fib-diagonal-eq t)
        ( issec-fib-diagonal-eq t)
        ( isretr-fib-diagonal-eq t)

-- Exercise 12.4 (c)

module _
  {l : Level} {A : UU l}
  where
  
  abstract
    is-trunc-is-trunc-map-diagonal :
      (k : 𝕋) → is-trunc-map k (diagonal A) → is-trunc (succ-𝕋 k) A
    is-trunc-is-trunc-map-diagonal k is-trunc-d x y =
      is-trunc-is-equiv' k
        ( fib (diagonal A) (pair x y))
        ( eq-fib-diagonal A (pair x y))
        ( is-equiv-eq-fib-diagonal A (pair x y))
        ( is-trunc-d (pair x y))

  abstract
    is-prop-is-contr-map-diagonal : is-contr-map (diagonal A) → is-prop A
    is-prop-is-contr-map-diagonal = is-trunc-is-trunc-map-diagonal neg-two-𝕋

  abstract
    is-set-is-prop-map-diagonal : is-prop-map (diagonal A) → is-set A
    is-set-is-prop-map-diagonal = is-trunc-is-trunc-map-diagonal neg-one-𝕋

  abstract
    is-set-is-emb-diagonal : is-emb (diagonal A) → is-set A
    is-set-is-emb-diagonal H =
      is-set-is-prop-map-diagonal (is-prop-map-is-emb H)

  abstract
    is-1-type-is-0-map-diagonal : is-0-map (diagonal A) → is-1-type A
    is-1-type-is-0-map-diagonal = is-trunc-is-trunc-map-diagonal zero-𝕋

  abstract
    is-1-type-is-faithful-diagonal : is-faithful (diagonal A) → is-1-type A
    is-1-type-is-faithful-diagonal H =
      is-1-type-is-0-map-diagonal (is-0-map-is-faithful H)
  
  abstract
    is-trunc-map-diagonal-is-trunc : 
      (k : 𝕋) → is-trunc (succ-𝕋 k) A → is-trunc-map k (diagonal A)
    is-trunc-map-diagonal-is-trunc k is-trunc-A t =
      is-trunc-is-equiv k
        ( Id (pr1 t) (pr2 t))
        ( eq-fib-diagonal A t)
        ( is-equiv-eq-fib-diagonal A t)
          ( is-trunc-A (pr1 t) (pr2 t))

  abstract
    is-contr-map-diagonal-is-prop : is-prop A → is-contr-map (diagonal A)
    is-contr-map-diagonal-is-prop = is-trunc-map-diagonal-is-trunc neg-two-𝕋

  abstract
    is-prop-map-diagonal-is-set : is-set A → is-prop-map (diagonal A)
    is-prop-map-diagonal-is-set = is-trunc-map-diagonal-is-trunc neg-one-𝕋

  abstract
    is-emb-diagonal-is-set : is-set A → is-emb (diagonal A)
    is-emb-diagonal-is-set H =
      is-emb-is-prop-map (is-prop-map-diagonal-is-set H)

  abstract
    is-0-map-diagonal-is-1-type : is-1-type A → is-0-map (diagonal A)
    is-0-map-diagonal-is-1-type = is-trunc-map-diagonal-is-trunc zero-𝕋

  abstract
    is-faithful-diagonal-is-1-type : is-1-type A → is-faithful (diagonal A)
    is-faithful-diagonal-is-1-type H =
      is-faithful-is-0-map (is-0-map-diagonal-is-1-type H)

diagonal-emb :
  {l : Level} (A : UU-Set l) → (type-Set A) ↪ ((type-Set A) × (type-Set A))
pr1 (diagonal-emb A) = diagonal (type-Set A)
pr2 (diagonal-emb A) = is-emb-diagonal-is-set (is-set-type-Set A)

diagonal-faithful-map :
  {l : Level} (A : UU-1-Type l) →
  faithful-map (type-1-Type A) (type-1-Type A × type-1-Type A)
pr1 (diagonal-faithful-map A) = diagonal (type-1-Type A)
pr2 (diagonal-faithful-map A) =
  is-faithful-diagonal-is-1-type (is-1-type-type-1-Type A)
```
