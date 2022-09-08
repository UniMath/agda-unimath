---
title: Russell's paradox
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.russells-paradox where

open import foundation.contractible-types using (is-contr-total-path')
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.empty-types using (empty)
open import foundation.equivalences using
  ( _≃_; id-equiv; equiv-precomp; _∘e_; inv-equiv; map-equiv; map-inv-equiv)
open import foundation.functoriality-cartesian-product-types using
  ( equiv-prod)
open import foundation.functoriality-dependent-pair-types using
  ( equiv-tot)
open import foundation.identity-types using (_＝_; refl; equiv-concat')
open import foundation.locally-small-types using (is-locally-small-UU)
open import foundation.multisets using (𝕍; comprehension-𝕍; _∉-𝕍_; _∈-𝕍_)
open import foundation.negation using (¬; no-fixed-points-neg)
open import foundation.small-multisets using
  ( is-small-𝕍; is-small-multiset-𝕍; is-small-comprehension-𝕍;
    is-small-∉-𝕍; resize-𝕍; is-small-resize-𝕍; equiv-elementhood-resize-𝕍;
    resize-resize-𝕍; eq-resize-𝕍)
open import foundation.small-types using
  ( is-small; is-small-lsuc; is-small-is-surjective; is-small')
open import foundation.small-universes using (is-small-universe)
open import foundation.surjective-maps using (is-surjective)
open import foundation.type-arithmetic-cartesian-product-types using
  ( commutative-prod)
open import foundation.type-arithmetic-dependent-pair-types using
  ( left-unit-law-Σ-is-contr; inv-assoc-Σ; assoc-Σ)
open import foundation.universal-multiset using
  ( universal-multiset-𝕍; is-small-universal-multiset-𝕍)
open import foundation.universe-levels using (Level; UU; lsuc)
```

## Idea

Russells paradox arises when a set of all sets is assumed to exist. In Russell's paradox it is of no importance that the elementhood relation takes values in propositions. In other words, Russells paradox arises similarly if there is a multiset of all multisets. We will construct Russell's paradox from the assumption that a universe `U` is equivalent to a type `A : U`. We conclude that there can be no universe that is contained in itself. Furthermore, using replacement we show that for any type `A : U`, there is no surjective map `A → U`.

## Definition

### Russell's multiset

```agda
Russell : (l : Level) → 𝕍 (lsuc l)
Russell l =
  comprehension-𝕍
    ( universal-multiset-𝕍 l)
    ( λ X → X ∉-𝕍 X)
```

## Properties

### If a universe is small with respect to another universe, then Russells multiset is also small

```agda
is-small-Russell :
  {l1 l2 : Level} → is-small-universe l2 l1 → is-small-𝕍 l2 (Russell l1)
is-small-Russell {l1} {l2} H =
  is-small-comprehension-𝕍 l2
    { lsuc l1}
    { universal-multiset-𝕍 l1}
    { λ z → z ∉-𝕍 z}
    ( is-small-universal-multiset-𝕍 l2 H)
    ( λ X → is-small-∉-𝕍 l2 {l1} {X} {X} (K X) (K X))
  where
  K = is-small-multiset-𝕍 (λ A → pr2 H A)

resize-Russell :
  {l1 l2 : Level} → is-small-universe l2 l1 → 𝕍 l2
resize-Russell {l1} {l2} H =
  resize-𝕍 (Russell l1) (is-small-Russell H)

is-small-resize-Russell :
  {l1 l2 : Level} (H : is-small-universe l2 l1) →
  is-small-𝕍 (lsuc l1) (resize-Russell H)
is-small-resize-Russell {l1} {l2} H =
  is-small-resize-𝕍 (Russell l1) (is-small-Russell H)

equiv-Russell-in-Russell :
  {l1 l2 : Level} (H : is-small-universe l2 l1) →
  (Russell l1 ∈-𝕍 Russell l1) ≃ (resize-Russell H ∈-𝕍 resize-Russell H)
equiv-Russell-in-Russell H =
  equiv-elementhood-resize-𝕍 (is-small-Russell H) (is-small-Russell H)
```

### Russell's paradox obtained from the assumption that `U` is `U`-small

```agda
paradox-Russell : {l : Level} → ¬ (is-small l (UU l))
paradox-Russell {l} H =
  no-fixed-points-neg
    ( R ∈-𝕍 R)
    ( pair (map-equiv β) (map-inv-equiv β))

  where
  
  K : is-small-universe l l
  K = pair H (λ X → pair X id-equiv)

  R : 𝕍 (lsuc l)
  R = Russell l
  
  is-small-R : is-small-𝕍 l R
  is-small-R = is-small-Russell K

  R' : 𝕍 l
  R' = resize-Russell K

  is-small-R' : is-small-𝕍 (lsuc l) R'
  is-small-R' = is-small-resize-Russell K

  abstract
    p : resize-𝕍 R' is-small-R' ＝ R
    p = resize-resize-𝕍 is-small-R

  α : (R ∈-𝕍 R) ≃ (R' ∈-𝕍 R')
  α = equiv-Russell-in-Russell K

  abstract
    β : (R ∈-𝕍 R) ≃ (R ∉-𝕍 R)
    β = ( equiv-precomp α empty) ∘e
        ( ( left-unit-law-Σ-is-contr
            { B = λ t → (pr1 t) ∉-𝕍 (pr1 t)}
            ( is-contr-total-path' R')
            ( pair R' refl)) ∘e
          ( ( inv-assoc-Σ (𝕍 l) (λ t → t ＝ R') (λ t → (pr1 t) ∉-𝕍 (pr1 t))) ∘e
            ( ( equiv-tot
                ( λ t →
                  ( commutative-prod) ∘e
                  ( equiv-prod
                    ( id-equiv)
                    ( inv-equiv
                      ( ( equiv-concat'
                          _ ( p)) ∘e
                        ( eq-resize-𝕍
                          ( is-small-multiset-𝕍 is-small-lsuc t)
                          ( is-small-R'))))))) ∘e
              ( assoc-Σ
                ( 𝕍 l)
                ( λ t → t ∉-𝕍 t)
                ( λ t → ( resize-𝕍
                          ( pr1 t)
                          ( is-small-multiset-𝕍 is-small-lsuc (pr1 t))) ＝
                        ( R))))))
```

### There can be no surjective map `f : A → U` for any `A : U`

```agda
no-surjection-onto-universe :
  {l : Level} {A : UU l} (f : A → UU l) → ¬ (is-surjective f)
no-surjection-onto-universe f H =
  paradox-Russell
    ( is-small-is-surjective H
      ( is-small')
      ( is-locally-small-UU))
```
