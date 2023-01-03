---
title: transport
---
description: a collection of transport lemmas not already in foundation.identity-types or foundation-core.identity-type
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation-core.transport where

open import foundation-core.cartesian-product-types
open import foundation-core.dependent-pair-types
open import foundation-core.equality-cartesian-product-types
open import foundation-core.identity-types
open import foundation-core.universe-levels
```

Transport through a family of cartesian products

```agda
tr-through-product :
  {l1 l2 : Level} {A : UU l1} {a0 a1 : A} (B C : A → UU l2) (p : a0 ＝ a1) (u : B a0 × C a0) →
  (tr (λ a → B a × C a) p u) ＝ (pair (tr B p (pr1 u)) (tr C p (pr2 u)))
tr-through-product B C refl u = refl
```

Transport over a base space that is a cartesian product

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {a0 a1 : A} {b0 b1 : B}
  where
  
  tr-over-product :
    (C : A × B → UU l3) (p : a0 ＝ a1) (q : b0 ＝ b1) (u : C (a0 , b0)) →
    (tr C (eq-pair p q) u) ＝ (tr (λ x → C (a1 , x)) q (tr (λ x → C (x , b0)) p u))
  tr-over-product C refl refl u = refl
```
preliminaries for a coherence path

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {a0 a1 : A} {b0 b1 : B}
  where
  tr-over-product-left-refl :
    (C : A × B → UU l3) (q : b0 ＝ b1) (u : C (a0 , b0)) →
    (tr C (eq-pair refl q) u) ＝ tr (λ x → C (a0 , x)) q u
  tr-over-product-left-refl C refl u = refl

  tr-over-product-right-refl :
    (C : A × B → UU l3) (p : a0 ＝ a1) (u : C (a0 , b0)) →
    (tr C (eq-pair p refl) u) ＝ tr (λ x → C (x , b0)) p u
  tr-over-product-right-refl C refl u = refl
```

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {a0 a1 : A} {b0 b1 : B} {p : a0 ＝ a1} {q : b0 ＝ b1}
    where

    expand-pair-outer : (eq-pair p q) ＝ ((eq-pair p refl) ∙ (eq-pair refl q))
    expand-pair-outer = ap (λ x → eq-pair x q) (inv right-unit) ∙ (eq-pair-concat p refl refl q)
```
The coherence path
```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {a0 a1 : A} {b0 b1 : B}
  where

  tr-over-product-coh : (C : A × B → UU l3) (p : a0 ＝ a1) (q : b0 ＝ b1) (u : C (a0 , b0)) →
    (tr-over-product C p q u) ＝ ((ap (λ x → tr C x u) expand-pair-outer)  ∙ (tr-concat (eq-pair p refl) (eq-pair refl q) u ∙ (
    (ap (tr C (eq-pair refl q)) (tr-over-product-right-refl C p u)) ∙  (tr-over-product-left-refl C q (tr (λ x → C (x , b0)) p u) ))))
  tr-over-product-coh C refl refl u = refl
```
Now for dependent pairs
