---
title: Univalent Mathematics in Agda
---

# Fiber inclusions

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundation.fiber-inclusions where

open import foundation.0-maps using (is-0-map)
open import foundation.1-types using
  ( is-1-type; UU-1-Type; type-1-Type; is-1-type-type-1-Type)
open import foundation.contractible-maps using
  ( is-contr-map; is-contr-map-is-equiv)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.embeddings using (is-emb; _↪_)
open import foundation.equality-dependent-pair-types using
  ( equiv-pair-eq-Σ)
open import foundation.equivalences using (_≃_; is-equiv-tr; _∘e_)
open import foundation.faithful-maps using
  ( is-faithful; is-faithful-is-0-map; faithful-map)
open import foundation.fibers-of-maps using (fib)
open import foundation.functoriality-dependent-pair-types using
  ( equiv-tot)
open import foundation.identity-types using (Id)
open import foundation.propositional-maps using
  ( is-prop-map; is-emb-is-prop-map)
open import foundation.propositions using (is-prop)
open import foundation.sets using (is-set; UU-Set; type-Set; is-set-type-Set)
open import foundation.type-arithmetic-cartesian-product-types using
  ( equiv-left-swap-Σ)
open import foundation.truncated-maps using (is-trunc-map)
open import foundation.truncated-types using
  ( is-trunc; is-trunc-equiv'; is-trunc-equiv)
open import foundation.truncation-levels using
  ( 𝕋; succ-𝕋; neg-two-𝕋; neg-one-𝕋; zero-𝕋)
open import foundation.type-arithmetic-dependent-pair-types using
  ( right-unit-law-Σ-is-contr)
open import foundation.unit-type using (raise-unit; raise-star)
open import foundation.universe-levels using (Level; UU)
```

## Definition

Given a family `B` of types over `A` and an element `a : A`, then the fiber inclusion of `B` at a is a map `B a → Σ A B`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2)
  where
  
  fiber-inclusion : (x : A) → B x → Σ A B
  pr1 (fiber-inclusion x y) = x
  pr2 (fiber-inclusion x y) = y

  fib-fiber-inclusion :
    (a : A) (t : Σ A B) → fib (fiber-inclusion a) t ≃ Id a (pr1 t)
  fib-fiber-inclusion a t =
    ( ( right-unit-law-Σ-is-contr
        ( λ p → is-contr-map-is-equiv (is-equiv-tr B p) (pr2 t))) ∘e
      ( equiv-left-swap-Σ)) ∘e
    ( equiv-tot (λ b → equiv-pair-eq-Σ (pair a b) t))
```

## Properties

### The fiber inclusions are truncated maps for any type family B if and only if A is truncated

```
module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1}
  where
  
  is-trunc-is-trunc-map-fiber-inclusion :
    ((B : A → UU l2) (a : A) → is-trunc-map k (fiber-inclusion B a)) →
    is-trunc (succ-𝕋 k) A
  is-trunc-is-trunc-map-fiber-inclusion H x y =
    is-trunc-equiv' k
      ( fib (fiber-inclusion B x) (pair y raise-star))
      ( fib-fiber-inclusion B x (pair y raise-star))
      ( H B x (pair y raise-star))
    where
    B : A → UU l2
    B a = raise-unit l2

  is-trunc-map-fiber-inclusion-is-trunc :
    (B : A → UU l2) (a : A) →
    is-trunc (succ-𝕋 k) A → is-trunc-map k (fiber-inclusion B a)
  is-trunc-map-fiber-inclusion-is-trunc B a H t =
    is-trunc-equiv k
      ( Id a (pr1 t))
      ( fib-fiber-inclusion B a t)
      ( H a (pr1 t))

module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2)
  where

  is-contr-map-fiber-inclusion :
    (x : A) → is-prop A → is-contr-map (fiber-inclusion B x)
  is-contr-map-fiber-inclusion =
    is-trunc-map-fiber-inclusion-is-trunc neg-two-𝕋 B

  is-prop-map-fiber-inclusion :
    (x : A) → is-set A → is-prop-map (fiber-inclusion B x)
  is-prop-map-fiber-inclusion =
    is-trunc-map-fiber-inclusion-is-trunc neg-one-𝕋 B

  is-0-map-fiber-inclusion :
    (x : A) → is-1-type A → is-0-map (fiber-inclusion B x)
  is-0-map-fiber-inclusion =
    is-trunc-map-fiber-inclusion-is-trunc zero-𝕋 B

  is-emb-fiber-inclusion : is-set A → (x : A) → is-emb (fiber-inclusion B x)
  is-emb-fiber-inclusion H x =
    is-emb-is-prop-map (is-prop-map-fiber-inclusion x H)

  is-faithful-fiber-inclusion :
    is-1-type A → (x : A) → is-faithful (fiber-inclusion B x)
  is-faithful-fiber-inclusion H x =
    is-faithful-is-0-map (is-0-map-fiber-inclusion x H)

fiber-inclusion-emb :
  {l1 l2 : Level} (A : UU-Set l1) (B : type-Set A → UU l2) →
  (x : type-Set A) → B x ↪ Σ (type-Set A) B
pr1 (fiber-inclusion-emb A B x) = fiber-inclusion B x
pr2 (fiber-inclusion-emb A B x) = is-emb-fiber-inclusion B (is-set-type-Set A) x

fiber-inclusion-faithful-map :
  {l1 l2 : Level} (A : UU-1-Type l1) (B : type-1-Type A → UU l2) →
  (x : type-1-Type A) → faithful-map (B x) (Σ (type-1-Type A) B)
pr1 (fiber-inclusion-faithful-map A B x) = fiber-inclusion B x
pr2 (fiber-inclusion-faithful-map A B x) =
  is-faithful-fiber-inclusion B (is-1-type-type-1-Type A) x
```
