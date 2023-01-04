---
title: transport
---
description: a collection of transport lemmas not already in foundation.identity-types or foundation-core.identity-type
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.transport where

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.equality-dependent-pair-types
open import foundation.functions
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.universe-levels
open import foundation.universal-property-dependent-pair-types
```

Transporting through along p through a family B ∘ f is transporting along ap f p through B. Useful when B≡id and f is a type family defined by univalence. 

```agda
tr-through-pre-comp :
  {l1 l2 l3 : Level} {A : UU l1} {a0 a1 : A} {B : UU l2} (f : A → B) (C : B → UU l3) (p : a0 ＝ a1) (u : C (f a0)) →
  (tr (C ∘ f) p u) ＝ (tr C (ap f p) u)
tr-through-pre-comp f C refl u = refl
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
tr-over-product :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {a0 a1 : A} {b0 b1 : B} (C : A × B → UU l3) (p : a0 ＝ a1) (q : b0 ＝ b1) (u : C (a0 , b0)) →
  (tr C (eq-pair p q) u) ＝ (tr (λ x → C (a1 , x)) q (tr (λ x → C (x , b0)) p u))
tr-over-product C refl refl u = refl
```

When one of the paths is refl.

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

A coherence path for transporting over a cartesian product, in case it is useful

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {a0 a1 : A} {b0 b1 : B} {p : a0 ＝ a1} {q : b0 ＝ b1}
    where

    expand-pair-outer : (eq-pair p q) ＝ ((eq-pair p refl) ∙ (eq-pair refl q))
    expand-pair-outer = ap (λ x → eq-pair x q) (inv right-unit) ∙ (eq-pair-concat p refl refl q)

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {a0 a1 : A} {b0 b1 : B}
  where
{- the following code works but pops up an error due to the agda version. Keep commented out until agda version is changed.

  tr-over-product-coh : (C : A × B → UU l3) (p : a0 ＝ a1) (q : b0 ＝ b1) (u : C (a0 , b0)) →
    (tr-over-product C p q u) ＝ ((ap (λ x → tr C x u) expand-pair-outer)  ∙ (tr-concat (eq-pair p refl) (eq-pair refl q) u ∙ (
    (ap (tr C (eq-pair refl q)) (tr-over-product-right-refl C p u)) ∙ (tr-over-product-left-refl C q (tr (λ x → C (x , b0)) p u) ))))
  tr-over-product-coh C refl refl u = refl -}
```

Now for dependent pairs. First, transporting through a family of dependent pairs.

```agda
tr-through-dependent-pair :
  {l1 l2 l3 : Level} {A : UU l1} {a0 a1 : A}  {B : A → UU l2} (C : (x : A) → B x → UU l3) (p : a0 ＝ a1) (z : Σ (B a0) (λ x → C a0 x)) →
  (tr (λ a → (Σ (B a) (λ x → C a x))) p z) ＝ pair (tr B p (pr1 z)) (tr (ind-Σ C) (eq-pair-Σ p refl) (pr2 z))
tr-through-dependent-pair C refl z = refl
```

Transporting over a base space of dependent pairs. 

```agda
tr-over-dependent-pair : {l1 l2 l3 : Level} {A : UU l1} {a0 a1 : A}  {B : A → UU l2} {b0 : B a0} {b1 : B a1}
  (C : (x : A) → B x → UU l3) (p : a0 ＝ a1) (q : path-over (B) p b0 b1) (u : C a0 b0) →
  (tr (ind-Σ C) (eq-pair-Σ p q) u) ＝ tr (λ x → C a1 x) q (tr (ind-Σ C) (eq-pair-Σ p refl) u)
tr-over-dependent-pair C refl refl u = refl
```

Transporting through a family of functions.

```agda
tr-through-function : {l1 l2 l3 : Level} {A : UU l1} {a0 a1 : A} (B : A → UU l2) (C : A → UU l3) (p : a0 ＝ a1) (f : B a0 → C a0) →
  (tr (λ a → B a → C a) p f) ＝ (λ x → tr C p (f (tr B (inv p) x)))
tr-through-function B C refl f = refl
```

Transporting through a family of identity types. Note that tr-id-right is already defined in foundation-core.identity-types

```agda
tr-id-left :
  {l1 : Level} {A : UU l1} {a b c : A} (q : Id b c) (p : Id b a) →
  Id (tr (λ y → Id y a) q p) ((inv q) ∙ p)
tr-id-left refl refl = refl

tr-id-two-sided :
  {l1 : Level} {A : UU l1} {a0 a1 : A} (q : a0 ＝ a1) (p : a0 ＝ a0) →
  (tr (λ y → y ＝ y) q p) ＝ (((inv q) ∙ p) ∙ q)
tr-id-two-sided refl p = inv right-unit

tr-through-fx＝gy :
  {l1 l2 l3 : Level} {A : UU l1} {a0 a1 : A} {B : UU l2} {b0 b1 : B} {C : UU l3} {f : A → C} {g : B → C} (p : a0 ＝ a1) (q : b0 ＝ b1) (s : f a0 ＝ g b0) → 
  (tr (λ z → (f (pr1 z)) ＝ (g (pr2 z))) (eq-pair p q) s) ＝ ((inv (ap f p)) ∙ (s ∙ (ap g q)))
tr-through-fx＝gy refl refl s = inv right-unit

tr-through-x＝y :
  {l1 l2 l3 : Level} {A : UU l1} {a0 a1 a2 a3 : A} (p : a0 ＝ a1) (q : a2 ＝ a3) (s : a0 ＝ a2) → 
  (tr (λ z → (pr1 z) ＝ (pr2 z)) (eq-pair p q) s) ＝ ((inv p) ∙ (s ∙ q))
tr-through-x＝y refl refl s = inv right-unit
```
