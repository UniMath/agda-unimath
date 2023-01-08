---
title: Dependent paths
---
description: We define the groupoidal operators on dependent paths, define the cohrences paths,
and then prove the operators are equivalences.
```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.dependent-paths where

open import foundation.identity-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functions
open import foundation.homotopies
open import foundation.universe-levels
```

Definitions of the groupoidal operators

```agda
module _
  {l1 l2 : Level} {A : UU l1} {a0 a1 a2 : A} (B : A → UU l2) {b0 : B a0} {b1 : B a1} {b2 : B a2}
   (p01 : a0 ＝ a1) (q01 : path-over B p01 b0 b1) (p12 : a1 ＝ a2) (q12 : path-over B p12 b1 b2)
  where

  d-concat : path-over B (p01 ∙ p12) b0 b2
  d-concat =   (tr-concat {B = B} p01 p12 b0)  ∙ ((ap (tr B p12) q01) ∙ (q12)) 

module _
  {l1 l2 : Level} {A : UU l1} {a0 a1 : A} (B : A → UU l2) (p01 : a0 ＝ a1) {b0 : B a0} {b1 : B a1}
  (q01 : path-over B p01 b0 b1)
  where
  
  d-inv : path-over B (inv p01) b1 b0
  d-inv =  (inv (ap (tr B (inv p01)) q01)) ∙ ((inv (tr-concat {B = B} (p01) (inv p01) b0)) ∙ (
    ap (λ t → tr B t b0) (right-inv p01))) 
```

Now we prove these paths satisfy identities analgous to the usual unit, inverse, and associativity laws.
Though, due to the dependent nature, the naive identities are not well typed. So these identities involve transporting.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {a0 a1 : A} (B : A → UU l2) {b0 : B a0} {b1  : B a1}
  where

  d-assoc :
    {a2 a3 : A} {b2 : B a2} {b3 : B a3} (p01 : a0 ＝ a1) (q01 : path-over B p01 b0 b1) (p12 : a1 ＝ a2)
    (q12 : path-over B p12 b1 b2) (p23 : a2 ＝ a3) (q23 : path-over B p23 b2 b3) →
    (tr (λ t → path-over B t b0 b3) (assoc p01 p12 p23) (d-concat B (p01 ∙ p12) (
    d-concat B p01 q01 p12 q12) p23 q23)) ＝ d-concat B p01 q01 (p12 ∙ p23) (d-concat B p12 q12 p23 q23)
  d-assoc refl refl p12 q12 p23 q23 = refl

  d-right-unit :
    (p : a0 ＝ a1) (q : path-over B p b0 b1) → (tr (λ t → path-over B t b0 b1) (right-unit) (
    d-concat B p q refl (refl-path-over B a1 b1))) ＝ q
  d-right-unit refl refl = refl

  d-left-unit : (p : a0 ＝ a1) (q : path-over B p b0 b1) →
    (tr (λ t → path-over B t b0 b1) (left-unit) (d-concat B refl (refl-path-over B a0 b0) p q)) ＝ q
  d-left-unit refl refl = refl

  d-right-inv : (p : a0 ＝ a1) (q : path-over B p b0 b1) →
    (tr (λ t → path-over B t b0 b0) (right-inv p) (d-concat B p q (inv p) (d-inv B p q))) ＝ (
     refl-path-over B a0 b0)
  d-right-inv refl refl = refl

  d-left-inv :  (p : a0 ＝ a1) (q : path-over B p b0 b1) →
    (tr (λ t → path-over B t b0 b0) (right-inv p) (d-concat B p q (inv p) (d-inv B p q))) ＝ (
     refl-path-over B a0 b0)
  d-left-inv refl refl = refl

  d-inv-d-inv : (p : a0 ＝ a1) (q : path-over B p b0 b1) →
    (tr (λ t → path-over B t b0 b1) (inv-inv p) (d-inv B (inv p) (d-inv B p q))) ＝ q
  d-inv-d-inv refl refl = refl

  distributive-d-inv-d-concat :
    {a2 : A} {b2 : B a2} (p01 : a0 ＝ a1) (q01 : path-over B p01 b0 b1) (p12 : a1 ＝ a2) (q12 : path-over B p12 b1 b2) →
    (tr (λ t → path-over B t b2 b0) (distributive-inv-concat p01 p12) (
    (d-inv B (p01 ∙ p12) (d-concat B p01 q01 p12 q12)))) ＝ (
    d-concat B (inv p12) (d-inv B p12 q12) (inv p01) (d-inv B p01 q01))
  distributive-d-inv-d-concat refl refl refl refl = refl
```
