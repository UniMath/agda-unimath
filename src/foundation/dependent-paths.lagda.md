---
title: dependent-paths
---
description: some of the path algebra of dependent paths

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

Define concatination and inverses of dependent paths

```agda
module _
  {l1 l2 : Level} {A : UU l1} {a0 a1 a2 : A} {p01 : a0 ＝ a1} {p12 : a1 ＝ a2} {B : A → UU l2} {b0 : B a0} {b1 : B a1} {b2 : B a2}
  (q01 : path-over B p01 b0 b1) (q12 : path-over B p12 b1 b2)
  where

  d-concat : path-over B (p01 ∙ p12) b0 b2
  d-concat = (tr-concat p01 p12 b0) ∙ ((ap (tr B p12) q01) ∙ (q12))

module _
  {l1 l2 : Level} {A : UU l1} {a0 a1 : A} {p01 : a0 ＝ a1} {B : A → UU l2} {b0 : B a0} {b1 : B a1}
  (q01 : path-over B p01 b0 b1)
  where
  
  d-inv : path-over B (inv p01) b1 b0
  d-inv = (inv (ap (tr B (inv p01)) q01)) ∙ ((inv (tr-concat (p01) (inv p01) b0)) ∙ (ap (λ t → tr B t b0) (right-inv p01)))
```

Now we prove these paths satisfy identities analgous to the usual unit, inverse, and associativity laws. Though, due to the dependent nature, the naive identities are not well typed. So these identities involve transporting.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {a0 a1 : A} {B : A → UU l2} {b0 : B a0} {b1  : B a1}
  where

  d-assoc : {a2 a3 : A} {b2 : B a2} {b3 : B a3} {p01 : a0 ＝ a1} {p12 : a1 ＝ a2} {p23 : a2 ＝ a3} (q01 : path-over B p01 b0 b1)
    (q12 : path-over B p12 b1 b2) (q23 : path-over B p23 b2 b3) → (d-concat (d-concat q01 q12) q23) ＝ (d-concat q01 (d-concat q12 q23))
  d-assoc {p01 = refl} {p12 = refl} {p23 = refl} q01 q12 q23 = refl

  d-right-unit : {p : a0 ＝ a1} (q : path-over B p b0 b1) → (tr (λ t → path-over B t b0 b1) (right-unit) (d-concat q (refl-path-over B a1 b1))) ＝ q
  d-right-unit {refl} q = refl

  d-left-unit : {p : a0 ＝ a1} (q : path-over B p b0 b1) → (tr (λ t → path-over B t b0 b1) (left-unit) (d-concat (refl-path-over B a0 b0) q)) ＝ q
  d-left-unit {refl} q = refl

  d-right-inv : {p : a0 ＝ a1} (q : path-over B p b0 b1) → (tr (λ t → path-over B t b0 b0) (right-inv p) (d-concat q (d-inv q))) ＝ (refl-path-over B a0 b0)
  d-right-inv {refl} q = refl

  d-left-inv :  {p : a0 ＝ a1} (q : path-over B p b0 b1) → (tr (λ t → path-over B t b0 b0) (right-inv p) (d-concat q (d-inv q))) ＝ (refl-path-over B a0 b0)
  d-left-inv {refl} q = refl

  d-inv-d-inv : {p : a0 ＝ a1} (q : path-over B p b0 b1) → (tr (λ t → path-over B t b0 b1) (inv-inv p) (d-inv (d-inv q))) ＝ q
  d-inv-d-inv {refl} q = refl

module _
  {l1 l2 : Level} {A : UU l1} {a0 a1 a2 : A} {B : A → UU l2} {b0 : B a0} {b1  : B a1} {b2 : B a2}
  where
  
  distributive-d-inv-d-concat : {p01 : a0 ＝ a1} {p12 : a1 ＝ a2} (q01 : path-over B p01 b0 b1) (q12 : path-over B p12 b1 b2) →
    (tr (λ t → path-over B t b2 b0) (distributive-inv-concat p01 p12) ((d-inv (d-concat q01 q12)))) ＝ (d-concat (d-inv q12) (d-inv q01))
  distributive-d-inv-d-concat {refl} {refl} q01 q12 = refl
```

The operations on dependent paths are equivalences

```agda
module _
  {l1 l2 : Level} {A : UU l1} {a0 a1 a2 : A} {p01 : a0 ＝ a1} {p12 : a1 ＝ a2} {B : A → UU l2} {b0 : B a0} {b1 : B a1} {b2 : B a2}
  where
  
  equiv-left-d-concat : (q01 : path-over B p01 b0 b1) → (path-over B p12 b1 b2) ≃ (path-over B (p01 ∙ p12) b0 b2)
  equiv-left-d-concat q01 = (λ t → (d-concat q01 t)) , is-equiv-has-inverse (λ t → (d-concat (d-inv q01) t)) α β where

    α : ((λ z → d-concat q01 z) ∘ (λ t → d-concat (d-inv q01) t)) ~ id
    α x = (inv (d-assoc q01 (d-inv q01) x)) ∙ (ap ((λ t → d-concat t x)) ((d-right-inv q01)))

    β : ((λ z → d-concat q01 z) ∘ (λ t → d-concat (d-inv q01) t)) ~ id
    β x = (inv (d-assoc (d-inv q01) q01 x)) ∙ (ap (λ t → d-concat t x) (d-left-inv q01))

  equiv-right-d-concat : (q12 : path-over B p12 b1 b2) → (path-over B p01 b0 b1) ≃ (path-over B (p01 ∙ p12) b0 b2)
  equiv-right-d-concat q12 = (λ t → d-concat t q12) , (is-equiv-has-inverse ((λ t → d-concat t (d-inv q12))) α β) where

    α : ((λ z → d-concat z q12) ∘ (λ t → d-concat t (d-inv q12))) ~ id
    α x = (inv (d-assoc x (d-inv q12) q12)) ∙ (ap (λ t → (d-concat x t)) (d-left-inv q12))

    β : ((λ t → d-concat t (d-inv q12)) ∘ (λ z → d-concat z q12)) ~ id
    β x = (inv (d-assoc x q12 (d-inv q12))) ∙ (ap (λ t → (d-concat x t)) (d-right-inv q12))

module _
  {l1 l2 : Level} {A : UU l1} {a0 a1 : A} {p01 : a0 ＝ a1} {B : A → UU l2} {b0 : B a0} {b1 : B a1}
  where

  equiv-d-inv : (path-over B p01 b0 b1) ≃ (path-over B (inv p01) b1 b0)
  equiv-d-inv = d-inv , (is-equiv-has-inverse ((tr (λ t → path-over B t b0 b1) (inv-inv p01) ∘ d-inv)) (α p01) (β p01) ) where

    α : (p' : a0 ＝ a1) → ((λ z → d-inv z) ∘ (tr (λ t → path-over B t b0 b1) (inv-inv p') ∘ d-inv)) ~ id
    α refl x = d-inv-d-inv x

    β : (p' : a0 ＝ a1) → ((λ z → d-inv z) ∘ (tr (λ t → path-over B t b0 b1) (inv-inv p') ∘ d-inv)) ~ id
    β refl x = d-inv-d-inv x
```

