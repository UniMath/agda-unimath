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

Useful later:

```agda
module _
  {l1 l2 : Level} {A : UU l1} {a0 a1 : A} {p0 p1 : a0 ＝ a1}
  (B : A → UU l2)
  where

  tr² : (α : p0 ＝ p1) (b0 : B a0) → (tr B p0 b0) ＝ (tr B p1 b0)
  tr² α b0 = ap (λ t → tr B t b0) α

{- Use transport lemmas when they become availible (i.e., when pr is merged) -}
coh-tr²-tr-tr :
  {l1 l2 : Level} {A : UU l1} {a0 a1 : A} {p0 p1 : a0 ＝ a1}
  (B : A → UU l2) {b0 : B a0} {b1 : B a1} (α : p0 ＝ p1)
  (q01 : path-over B p0 b0 b1) → 
  (tr (λ t → path-over B t b0 b1) α q01) ＝ (inv (tr² B α b0) ∙ q01)
coh-tr²-tr-tr B refl q01 = refl

module _
  {l1 l2 : Level} {A : UU l1} {a0 a1 : A} {p0 p1 : a0 ＝ a1}
  (B : A → UU l2) (α : p0 ＝ p1) {b0 : B a0} {b1 : B a1}
  (q0 : path-over B p0 b0 b1) (q1 : path-over B p1 b0 b1)
  where

  path-over² : UU l2
  path-over² = q0 ＝ ((tr² B α b0) ∙ q1)

  tr-path-over-path-over² :
    (path-over²) → ((tr (λ t → path-over B t b0 b1) α q0) ＝ q1)
  tr-path-over-path-over² z = coh-tr²-tr-tr B α q0 ∙ (
    (map-inv-equiv (equiv-inv-con (inv (tr² B α b0)) q0 q1)
    (z ∙ inv (ap (λ t → t ∙ q1) (inv-inv (tr² B α b0))))))
```

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

Now we prove these paths satisfy identities analgous to the usual unit, inverse, and associativity laws. Though, due to the dependent nature, the naive identities are not well typed. So these identities involve transporting.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {a0 a1 : A} (B : A → UU l2) {b0 : B a0} {b1  : B a1}
  where

  d-assoc :
    {a2 a3 : A} {b2 : B a2} {b3 : B a3}
    (p01 : a0 ＝ a1) (q01 : path-over B p01 b0 b1) (p12 : a1 ＝ a2)
    (q12 : path-over B p12 b1 b2) (p23 : a2 ＝ a3) (q23 : path-over B p23 b2 b3) → 
    path-over² B (assoc p01 p12 p23)
      (d-concat B (p01 ∙ p12) (d-concat B p01 q01 p12 q12) p23 q23)
      (d-concat B p01 q01 (p12 ∙ p23) (d-concat B p12 q12 p23 q23))
  d-assoc refl refl p12 q12 p23 q23 = refl

  d-assoc' :
    {a2 a3 : A} {b2 : B a2} {b3 : B a3}
    (p01 : a0 ＝ a1) (q01 : path-over B p01 b0 b1) (p12 : a1 ＝ a2)
    (q12 : path-over B p12 b1 b2) (p23 : a2 ＝ a3) (q23 : path-over B p23 b2 b3) →
    (tr (λ t → path-over B t b0 b3) (assoc p01 p12 p23) (d-concat B (p01 ∙ p12) (
    d-concat B p01 q01 p12 q12) p23 q23)) ＝
    d-concat B p01 q01 (p12 ∙ p23) (d-concat B p12 q12 p23 q23)
  d-assoc' p01 q01 p12 q12 p23 q23 = tr-path-over-path-over² B (assoc p01 p12 p23)
     (d-concat B (p01 ∙ p12) (d-concat B p01 q01 p12 q12) p23 q23)
     (d-concat B p01 q01 (p12 ∙ p23) (d-concat B p12 q12 p23 q23)) (d-assoc p01 q01 p12 q12 p23 q23)

  d-right-unit : (p : a0 ＝ a1) (q : path-over B p b0 b1) →
    path-over² B (right-unit {p = p}) (d-concat B p q refl (refl-path-over B a1 b1)) q
  d-right-unit refl refl = refl

  d-right-unit' :
    (p : a0 ＝ a1) (q : path-over B p b0 b1) → (tr (λ t → path-over B t b0 b1) (right-unit) (
    d-concat B p q refl (refl-path-over B a1 b1))) ＝ q
  d-right-unit' p q = tr-path-over-path-over² B (right-unit {p = p})
    (d-concat B p q refl (refl-path-over B a1 b1)) q (d-right-unit p q)

  d-left-unit : (p : a0 ＝ a1) (q : path-over B p b0 b1) →
    path-over² B (left-unit {p = p}) (d-concat B refl (refl-path-over B a0 b0) p q) q
  d-left-unit p q = refl

  d-left-unit' : (p : a0 ＝ a1) (q : path-over B p b0 b1) →
    (tr (λ t → path-over B t b0 b1) (left-unit) (d-concat B refl (refl-path-over B a0 b0) p q)) ＝ q
  d-left-unit' p q = tr-path-over-path-over² B (left-unit {p = p})
    (d-concat B refl (refl-path-over B a0 b0) p q) q (d-left-unit p q)

  d-right-inv : (p : a0 ＝ a1) (q : path-over B p b0 b1) →
    path-over² B (right-inv p) (d-concat B p q (inv p) (d-inv B p q))
    (refl-path-over B a0 b0)
  d-right-inv refl refl = refl

  d-right-inv' : (p : a0 ＝ a1) (q : path-over B p b0 b1) →
    (tr (λ t → path-over B t b0 b0) (right-inv p) (d-concat B p q (inv p) (d-inv B p q))) ＝ (
     refl-path-over B a0 b0)
  d-right-inv' p q  = tr-path-over-path-over² B (right-inv p)
    (d-concat B p q (inv p) (d-inv B p q)) (refl-path-over B a0 b0) (d-right-inv p q)

  d-left-inv : (p : a0 ＝ a1) (q : path-over B p b0 b1) →
    path-over² B (left-inv p) (d-concat B (inv p) (d-inv B p q) p q) (refl-path-over B a1 b1)
  d-left-inv refl refl = refl

  d-left-inv' :  (p : a0 ＝ a1) (q : path-over B p b0 b1) →
    (tr (λ t → path-over B t b1 b1) (left-inv p) (d-concat B (inv p) (d-inv B p q) p q)) ＝ (
     refl-path-over B a1 b1)
  d-left-inv' p q = tr-path-over-path-over² B (left-inv p)
    (d-concat B (inv p) (d-inv B p q) p q) (refl-path-over B a1 b1) (d-left-inv p q)

  d-inv-d-inv : (p : a0 ＝ a1) (q : path-over B p b0 b1) →
    path-over² B (inv-inv p) (d-inv B (inv p) (d-inv B p q)) q
  d-inv-d-inv refl refl = refl
  
  d-inv-d-inv' : (p : a0 ＝ a1) (q : path-over B p b0 b1) →
    (tr (λ t → path-over B t b0 b1) (inv-inv p) (d-inv B (inv p) (d-inv B p q))) ＝ q
  d-inv-d-inv' p q = tr-path-over-path-over² B (inv-inv p)
    (d-inv B (inv p) (d-inv B p q)) q (d-inv-d-inv p q)

  distributive-d-inv-d-concat :
    {a2 : A} {b2 : B a2} (p01 : a0 ＝ a1) (q01 : path-over B p01 b0 b1)
    (p12 : a1 ＝ a2) (q12 : path-over B p12 b1 b2) →
    path-over² B (distributive-inv-concat p01 p12) 
    (d-inv B (p01 ∙ p12) (d-concat B p01 q01 p12 q12))
    (d-concat B (inv p12) (d-inv B p12 q12) (inv p01) (d-inv B p01 q01))
  distributive-d-inv-d-concat refl refl refl refl = refl

  distributive-d-inv-d-concat' :
    {a2 : A} {b2 : B a2} (p01 : a0 ＝ a1) (q01 : path-over B p01 b0 b1)
    (p12 : a1 ＝ a2) (q12 : path-over B p12 b1 b2) →
    (tr (λ t → path-over B t b2 b0) (distributive-inv-concat p01 p12) (
    (d-inv B (p01 ∙ p12) (d-concat B p01 q01 p12 q12)))) ＝ (
    d-concat B (inv p12) (d-inv B p12 q12) (inv p01) (d-inv B p01 q01))
  distributive-d-inv-d-concat' p01 q01 p12 q12 = tr-path-over-path-over² B
    (distributive-inv-concat p01 p12) (d-inv B (p01 ∙ p12) (d-concat B p01 q01 p12 q12))
    (d-concat B (inv p12) (d-inv B p12 q12) (inv p01) (d-inv B p01 q01)) (distributive-d-inv-d-concat p01 q01 p12 q12)
```

The operations on dependent paths are equivalences

```agda

{-
module _
  {l1 l2 : Level} {A : UU l1} {a0 a1 a2 : A} {B : A → UU l2} {b0 : B a0} {b1 : B a1} {b2 : B a2}
  where

  inv-left-d-concat : (p01 : a0 ＝ a1) (q01 : path-over B p01 b0 b1) (p12 : a1 ＝ a2) →
    (path-over B (p01 ∙ p12) b0 b2) → (path-over B p12  b1 b2)
  inv-left-d-concat p01 q01 p12 = (tr (λ t' → path-over B t' b1 b2) ((inv (assoc (inv p01) p01 p12)) ∙ (
    ap (λ t → t ∙ p12) (left-inv p01)))) ∘ (d-concat B (inv p01) (d-inv B p01 q01) (p01 ∙ p12))



  issec-inv-left-d-concat' : (p01 : a0 ＝ a1) (q01 : path-over B p01 b0 b1) (p12 : a1 ＝ a2) →
    ((λ z → d-concat B p01 q01 p12 z) ∘ (inv-left-d-concat p01 q01 p12)) ~ id
  issec-inv-left-d-concat' refl refl refl refl = refl

  isretr-inv-left-d-concat' : (p01 : a0 ＝ a1) (q01 : path-over B p01 b0 b1) (p12 : a1 ＝ a2) →
    ((inv-left-d-concat p01 q01 p12) ∘ (λ z → d-concat B p01 q01 p12 z)) ~ id
  isretr-inv-left-d-concat' refl refl refl refl = refl

  is-equiv-left-d-concat : (p01 : a0 ＝ a1) (q01 : path-over B p01 b0 b1) (p12 : a1 ＝ a2) →
    is-equiv (λ (t : path-over B p12 b1 b2) → d-concat B p01 q01 p12 t)
  is-equiv-left-d-concat p01 q01 p12 =  is-equiv-has-inverse ((inv-left-d-concat p01 q01 p12))  (
    issec-inv-left-d-concat' p01 q01 p12) (isretr-inv-left-d-concat' p01 q01 p12)

  equiv-left-d-concat : (p01 : a0 ＝ a1) (q01 : path-over B p01 b0 b1) (p12 : a1 ＝ a2) →
    (path-over B p12 b1 b2) ≃ (path-over B (p01 ∙ p12) b0 b2)
  equiv-left-d-concat p01 q01 p12 = (λ t → (d-concat B p01 q01 p12 t)) , (
    is-equiv-left-d-concat p01 q01 p12)

  coh-com-sq-d-concat-tr : (p01 : a0 ＝ a1) (q01 : path-over B p01 b0 b1)
    (p12 : a1 ＝ a2) (q12' : path-over B (inv p01 ∙ (p01 ∙ p12)) b1 b2) →
    (square-function-htpy (tr (λ t → path-over B t b1 b2) (
    inv (assoc (inv p01) p01 p12) ∙ (ap (λ t → t ∙ p12) (left-inv p01)))) (d-concat B p01 q01 p12)
    ((d-concat B p01 q01 (inv p01 ∙ (p01 ∙ p12)))) (tr (λ t → path-over B (p01 ∙ t) b0 b2) (
    inv (assoc (inv p01) p01 p12) ∙ (ap (λ t → t ∙ p12) (left-inv p01)))) q12')
  coh-com-sq-d-concat-tr p01 q01 p12 q12' = preserves-tr (
    λ t → d-concat B p01 q01 t) (inv (assoc (inv p01) p01 p12) ∙ (ap (λ t → t ∙ p12) (left-inv p01))) q12'



  
(tr (λ t → path-over B (p01 ∙ t) b0 b2) (  (inv (assoc (inv p01) p01 p12)) ∙ (
    ap ( _∙ p12) (right-inv p01) ) ))
    
    (  ∘ (
    (inv (assoc (inv p01) p01 p12)) ∙ ( ap ( _∙ p12) (right-inv p01) ) ))) q12') ＝
    ( ( ∘ (d-concat p01 q01 ( (inv p01) ∙ (p01 ∙ p12) ) )) q12' ) -}
{- THERE HAS TO BE A BETTER WAY
  issec-inv-left-d-concat : (p01 : a0 ＝ a1) (q01 : path-over B p01 b0 b1)
    (p12 : a1 ＝ a2) (q02 : path-over B (p01 ∙ p12) b0 b2) →
    (((λ z → d-concat B p01 q01 p12 z) ∘
    (inv-left-d-concat p01 q01 p12)) q02) ＝ q02
  issec-inv-left-d-concat p01 q01 p12 q02 = coh-com-sq-d-concat-tr
    p01 q01 p12 (d-concat B (inv p01) (d-inv B p01 q01) ((p01 ∙ p12)) q02) ∙
    ((ap (λ x → tr (λ t → path-over B (p01 ∙ t) b0 b2)
    (inv (assoc (inv p01) p01 p12) ∙ ap (λ t → t ∙ p12) (left-inv p01)) x)
    ( (inv (d-assoc B p01 q01 (inv p01) (d-inv B p01 q01 ) (p01 ∙ p12) q02)) )) ∙ (ap
    (λ x → tr (λ t → path-over B (p01 ∙ t) b0 b2)
    (inv (assoc (inv p01) p01 p12) ∙ ap (λ t → t ∙ p12) (left-inv p01))
    (tr (λ t → path-over B t b0 b2) (assoc p01 (inv p01) (p01 ∙ p12))
    (d-concat B (p01 ∙ inv p01) x (p01 ∙ p12) q02)))
    ((eq-transpose-tr' (right-inv p01) (d-right-inv B p01 q01))) ∙ ({!!} ∙ {!!})))
 

for (inv p0 ∙ (p01 ∙ p12)) ＝ p12, use the path inv (assoc (inv p01) p01 p12) ∙ (ap (λ t → t ∙ p12) (left-inv p01))
 (eq-transpose-tr' {B = (λ t → path-over B t b0 b2)} {!!}
ap (λ t → p01 ∙ t) (inv (assoc (inv p01) p01 p12) ∙ (ap (λ t → t ∙ p12) (left-inv p01)))
-}
