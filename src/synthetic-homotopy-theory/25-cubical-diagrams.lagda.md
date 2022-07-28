---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --allow-unsolved-metas --exact-split #-}

module synthetic-homotopy-theory.25-cubical-diagrams where

open import foundation.commuting-cubes
open import foundation.commuting-squares
open import foundation.cones-pullbacks
open import foundation.contractible-types
open import foundation.descent-equivalences
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.functions
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-fibers-of-maps
open import foundation.homotopies
open import foundation.identity-types
open import foundation.pullbacks
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universal-property-pullbacks
open import foundation.universe-levels

open import synthetic-homotopy-theory.24-pushouts


{- We show that identity types commute with pullbacks. -}

{- Next we show that for any commuting cube, if the bottom and top squares are
   pullback squares, then so is the square of fibers of the vertical maps in
   cube. -}

{-

square-fib-cube :
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : A → C) (h : B → D) (k : C → D)
  {A' : UU l1'} {B' : UU l2'} {C' : UU l3'} {D' : UU l4'}
  (f' : A' → B') (g' : A' → C') (h' : B' → D') (k' : C' → D')
  (hA : A' → A) (hB : B' → B) (hC : C' → C) (hD : D' → D)
  (top : (h' ∘ f') ~ (k' ∘ g'))
  (back-left : (f ∘ hA) ~ (hB ∘ f'))
  (back-right : (g ∘ hA) ~ (hC ∘ g'))
  (front-left : (h ∘ hB) ~ (hD ∘ h'))
  (front-right : (k ∘ hC) ~ (hD ∘ k'))
  (bottom : (h ∘ f) ~ (k ∘ g)) →
  (c : coherence-cube f g h k f' g' h' k' hA hB hC hD
       top back-left back-right front-left front-right bottom) →
  (a : A) →
  ( ( tot (λ d' p → p ∙ (bottom a)) ∘
      ( map-fib-cone h hD (pair hB (pair h' front-left)) (f a))) ∘
    ( map-fib-cone f hB (pair hA (pair f' back-left)) a)) ~
  ( ( map-fib-cone k hD (pair hC (pair k' front-right)) (g a)) ∘
    ( map-fib-cone g hC (pair hA (pair g' back-right)) a))
square-fib-cube f g h k f' g' h' k' hA hB hC hD
  top back-left back-right front-left front-right bottom c
  .(hA a') (pair a' refl) =
  eq-pair-Σ
    ( pair
      ( top a')
      ( ( tr-id-left-subst
          ( top a')
          ( k (g (hA a')))
          ( ( ( inv (front-left (f' a'))) ∙
              ( ap h ((inv (back-left a')) ∙ refl))) ∙
            ( bottom (hA a')))) ∙
        ( ( ( assoc (inv (ap hD (top a'))) _ (bottom (hA a'))) ∙
            {!!}) ∙
          ( distributive-inv-concat (ap k (back-right a')) (front-right (g' a')) ∙
            ( ( ap
                ( concat (inv (front-right (g' a'))) ?)
                ( inv (ap-inv k (back-right a')))) ∙
              ( ap
                ( concat (inv (front-right (g' a'))) ?)
                ( ap (ap k) (inv right-unit))))))))
-}
```
