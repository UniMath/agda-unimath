# Functoriality of set quotients

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.functoriality-set-quotients where

open import foundation.commuting-squares using (coherence-square)
open import foundation.contractible-types using (is-contr; center)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalence-relations using (Eq-Rel; type-Eq-Rel)
open import foundation.functions using (_∘_)
open import foundation.reflecting-maps-equivalence-relations using
  ( reflecting-map-Eq-Rel; map-reflecting-map-Eq-Rel;
    reflects-map-reflecting-map-Eq-Rel)
open import foundation.sets using (UU-Set; type-Set)
open import foundation.universal-property-set-quotients using
  ( is-set-quotient; universal-property-set-quotient-is-set-quotient)
open import foundation.universe-levels using (Level; UU)
```

## Idea

Set quotients act functorially on types equipped with equivalence relations.

## Definition

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} (R : Eq-Rel l2 A)
  (A/R : UU-Set l3) (f : reflecting-map-Eq-Rel R (type-Set A/R))
  {B : UU l4} (S : Eq-Rel l5 B)
  (B/S : UU-Set l6) (g : reflecting-map-Eq-Rel S (type-Set B/S))
  where

  unique-map-is-set-quotient :
    ({l : Level} → is-set-quotient l R A/R f) →
    ({l : Level} → is-set-quotient l S B/S g) →
    (h : A → B) → ({x y : A} → type-Eq-Rel R x y → type-Eq-Rel S (h x) (h y)) →
    is-contr
      ( Σ ( type-Set A/R → type-Set B/S)
          ( coherence-square h
            ( map-reflecting-map-Eq-Rel R f)
            ( map-reflecting-map-Eq-Rel S g)))
  unique-map-is-set-quotient Uf Ug h Hh =
    universal-property-set-quotient-is-set-quotient R A/R f Uf B/S
      ( pair
        ( map-reflecting-map-Eq-Rel S g ∘ h)
        ( λ r → reflects-map-reflecting-map-Eq-Rel S g (Hh r)))

  map-is-set-quotient :
    ({l : Level} → is-set-quotient l R A/R f) →
    ({l : Level} → is-set-quotient l S B/S g) →
    (h : A → B) → ({x y : A} → type-Eq-Rel R x y → type-Eq-Rel S (h x) (h y)) →
    type-Set A/R → type-Set B/S
  map-is-set-quotient Uf Ug h H =
    pr1 (center (unique-map-is-set-quotient Uf Ug h H))

  coherence-square-map-is-set-quotient :
    (Uf : {l : Level} → is-set-quotient l R A/R f) →
    (Ug : {l : Level} → is-set-quotient l S B/S g) →
    (h : A → B)
    (H : {x y : A} → type-Eq-Rel R x y → type-Eq-Rel S (h x) (h y)) →
    coherence-square h
      ( map-reflecting-map-Eq-Rel R f)
      ( map-reflecting-map-Eq-Rel S g)
      ( map-is-set-quotient Uf Ug h H)
  coherence-square-map-is-set-quotient Uf Ug h H =
    pr2 (center (unique-map-is-set-quotient Uf Ug h H))
```
