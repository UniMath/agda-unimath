---
title: Binary functoriality of set quotients
---

```agda
module foundation.binary-functoriality-set-quotients where

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalence-relations
open import foundation.identity-types
open import foundation.reflecting-maps-equivalence-relations
open import foundation.sets
open import foundation.universal-property-set-quotients
open import foundation.universe-levels
```

## Idea

Given three types `A`, `B`, and `C` equipped with equivalence relations `R`, `S`, and `T`, respectively, any binary operation `f : A → B → C` such that for any `x x' : A` such that `R x x'` holds, and for any `y y' : B` such that `S y y'` holds, the relation `T (f x y) (f x' y')` holds extends uniquely to a binary operation `g : A/R → B/S → C/T` such that `g (q x) (q y) = q (f x y)` for all `x : A` and `y : B`.

## Definition

### Binary functoriality of types that satisfy the universal property of set quotients

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 l9 : Level}
  {A : UU l1} (R : Eq-Rel l2 A)
  (QR : Set l3) (qR : reflecting-map-Eq-Rel R (type-Set QR))
  {B : UU l4} (S : Eq-Rel l5 B)
  (QS : Set l6) (qS : reflecting-map-Eq-Rel S (type-Set QS))
  {C : UU l7} (T : Eq-Rel l8 C)
  (QT : Set l9) (qT : reflecting-map-Eq-Rel T (type-Set QT))
  where


--   unique-binary-map-set-quotient :
--     ({l : Level} → is-set-quotient l R QR qR) →
--     ({l : Level} → is-set-quotient l S QS qS) →
--     ({l : Level} → is-set-quotient l T QT qT) →
--     (f : A → B → C)
--     (H : {x x' : A} {y y' : B} →
--        sim-Eq-Rel R x x' → sim-Eq-Rel S y y' → sim-Eq-Rel T (f x y) (f x' y')) →
--     is-contr
--       ( Σ ( type-Set QR → type-Set QS → type-Set QT)
--           ( λ h →
--             (x : A) (y : B) →
--             ( h ( map-reflecting-map-Eq-Rel R qR x)
--                 ( map-reflecting-map-Eq-Rel S qS y)) ＝
--             ( map-reflecting-map-Eq-Rel T qT (f x y))))
--   unique-binary-map-set-quotient UqR UqS UqT f H =
--     {!universal-property-set-quotient-is-set-quotient R QR qR UqR ? ?!}

```

### Binary functoriality of set quotients


