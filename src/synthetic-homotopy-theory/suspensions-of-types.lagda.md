---
title: Suspensions of types
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module synthetic-homotopy-theory.suspensions-of-types where

open import elementary-number-theory.natural-numbers

open import foundation.booleans
open import foundation.constant-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.functions
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.transport
open import foundation.unit-type
open import foundation.universal-property-unit-type
open import foundation.universe-levels

open import synthetic-homotopy-theory.24-pushouts
open import synthetic-homotopy-theory.cocones-pushouts
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.universal-property-pushouts
```

## Definition

### Suspension of ordinary types

```agda
suspension-structure :
  {l1 l2 : Level} (X : UU l1) (Y : UU l2) → UU (l1 ⊔ l2)
suspension-structure X Y = Σ Y (λ N → Σ Y (λ S → (x : X) → Id N S))

suspension-cocone' :
  {l1 l2 : Level} (X : UU l1) (Y : UU l2) → UU (l1 ⊔ l2)
suspension-cocone' X Y = cocone (const X unit star) (const X unit star) Y

cocone-suspension-structure :
  {l1 l2 : Level} (X : UU l1) (Y : UU l2) →
  suspension-structure X Y → suspension-cocone' X Y
cocone-suspension-structure X Y (pair N (pair S merid)) =
  pair
    ( const unit Y N)
    ( pair
      ( const unit Y S)
      ( merid))

universal-property-suspension' :
  (l : Level) {l1 l2 : Level} (X : UU l1) (Y : UU l2)
  (susp-str : suspension-structure X Y) → UU (lsuc l ⊔ l1 ⊔ l2)
universal-property-suspension' l X Y susp-str-Y =
  universal-property-pushout l
    ( const X unit star)
    ( const X unit star)
    ( cocone-suspension-structure X Y susp-str-Y)

is-suspension :
  (l : Level) {l1 l2 : Level} (X : UU l1) (Y : UU l2) → UU (lsuc l ⊔ l1 ⊔ l2)
is-suspension l X Y =
  Σ (suspension-structure X Y) (universal-property-suspension' l X Y)

suspension :
  {l : Level} → UU l → UU l
suspension X = pushout (const X unit star) (const X unit star)

N-susp :
  {l : Level} {X : UU l} → suspension X
N-susp {X = X} = inl-pushout (const X unit star) (const X unit star) star

S-susp :
  {l : Level} {X : UU l} → suspension X
S-susp {X = X} = inr-pushout (const X unit star) (const X unit star) star

merid-susp :
  {l : Level} {X : UU l} → X → Id (N-susp {X = X}) (S-susp {X = X})
merid-susp {X = X} = glue-pushout (const X unit star) (const X unit star)

susp-struct :
  {l : Level} (X : UU l) → suspension-structure X (suspension X)
susp-struct X = (N-susp , S-susp , merid-susp)

sphere : ℕ → UU lzero
sphere zero-ℕ = bool
sphere (succ-ℕ n) = suspension (sphere n)

N-sphere : (n : ℕ) → sphere n
N-sphere zero-ℕ = true
N-sphere (succ-ℕ n) = N-susp

S-sphere : (n : ℕ) → sphere n
S-sphere zero-ℕ = false
S-sphere (succ-ℕ n) = S-susp
```

## Properties

### The universal property of the suspension as a pushout

```agda
suspension-cocone :
  {l1 l2 : Level} (X : UU l1) (Z : UU l2) → UU _
suspension-cocone X Z = Σ Z (λ z1 → Σ Z (λ z2 → (x : X) → Id z1 z2))

suspension-cocone-N :
  {l1 l2 : Level} {X : UU l1} {Z : UU l2} (c : suspension-cocone X Z) → Z
suspension-cocone-N c = pr1 c

suspension-cocone-S :
  {l1 l2 : Level} {X : UU l1} {Z : UU l2} (c : suspension-cocone X Z) → Z
suspension-cocone-S c = pr1 (pr2 c)

suspension-cocone-merid :
  {l1 l2 : Level} {X : UU l1} {Z : UU l2} (c : suspension-cocone X Z) →
  (x : X) → ((suspension-cocone-N c) ＝ (suspension-cocone-S c))
suspension-cocone-merid c = pr2 (pr2 c)

{- Characterization of equalities in the above type -}

suspension-cocone-htpy : {l1 l2 : Level} {X : UU l1} {Z : UU l2} 
  (c c' : suspension-cocone X Z) → UU (l1 ⊔ l2)
suspension-cocone-htpy {X = X} c c' = Σ ((suspension-cocone-N c) ＝ (suspension-cocone-N c'))
  (λ p → Σ ((suspension-cocone-S c) ＝ (suspension-cocone-S c'))
  (λ q → (x : X) → (((inv p) ∙ (suspension-cocone-merid c x)) ∙ q) ＝ (suspension-cocone-merid c' x)))

suspension-cocone-eq-suspension-cocone-htpy : {l1 l2 : Level} {X : UU l1} {Z : UU l2} 
  {c c' : suspension-cocone X Z} → (suspension-cocone-htpy c c') → (c ＝ c')
suspension-cocone-eq-suspension-cocone-htpy {X = X} {c = c} {c' = c'} H = eq-pair-Σ (pr1 H) (tr-Σ (λ z1 → λ z2 → X → Id z1 z2) (pr1 H) (pr2 c) ∙ (eq-pair-Σ (tr-const (pr1 H) (pr1 (pr2 c)) ∙ (pr1 (pr2 H))) {!tr-function-type (λ z2 → X) (λ z2 → Id (pr1 c') z2) (tr-const (pr1 H) (pr1 (pr2 c)) ∙ pr1 (pr2 H)) (pr2 (pr2 c'))!}))
{- (tr-const (pr1 H) (pr1 (pr2 c)) ∙ pr1 (pr2 H))
      (tr (ind-Σ (λ z1 z2 → X → Id z1 z2)) (eq-pair-Σ (pr1 H) refl) -}
ev-suspension :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} →
  (susp-str-Y : suspension-structure X Y) →
  (Z : UU l3) → (Y → Z) → suspension-cocone X Z
ev-suspension (pair N (pair S merid)) Z h =
  pair (h N) (pair (h S) (h ·l merid))

universal-property-suspension :
  (l : Level) {l1 l2 : Level} (X : UU l1) (Y : UU l2) →
  suspension-structure X Y → UU (lsuc l ⊔ l1 ⊔ l2)
universal-property-suspension l X Y susp-str-Y =
  (Z : UU l) → is-equiv (ev-suspension susp-str-Y Z)

comparison-suspension-cocone :
  {l1 l2 : Level} (X : UU l1) (Z : UU l2) →
  suspension-cocone' X Z ≃ suspension-cocone X Z
comparison-suspension-cocone X Z =
  equiv-Σ
    ( λ z1 → Σ Z (λ z2 → (x : X) → Id z1 z2))
    ( equiv-universal-property-unit Z)
    ( λ z1 →
      equiv-Σ
        ( λ z2 → (x : X) → Id (z1 star) z2)
        ( equiv-universal-property-unit Z)
        ( λ z2 → id-equiv))

map-comparison-suspension-cocone :
  {l1 l2 : Level} (X : UU l1) (Z : UU l2) →
  suspension-cocone' X Z → suspension-cocone X Z
map-comparison-suspension-cocone X Z =
  map-equiv (comparison-suspension-cocone X Z)

is-equiv-map-comparison-suspension-cocone :
  {l1 l2 : Level} (X : UU l1) (Z : UU l2) →
  is-equiv (map-comparison-suspension-cocone X Z)
is-equiv-map-comparison-suspension-cocone X Z =
  is-equiv-map-equiv (comparison-suspension-cocone X Z)

triangle-ev-suspension :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} →
  (susp-str-Y : suspension-structure X Y) →
  (Z : UU l3) →
  ( ( map-comparison-suspension-cocone X Z) ∘
    ( cocone-map
      ( const X unit star)
      ( const X unit star)
      ( cocone-suspension-structure X Y susp-str-Y))) ~
  ( ev-suspension susp-str-Y Z)
triangle-ev-suspension (pair N (pair S merid)) Z h = refl

is-equiv-ev-suspension :
  { l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} →
  ( susp-str-Y : suspension-structure X Y) →
  ( up-Y : universal-property-suspension' l3 X Y susp-str-Y) → 
  ( Z : UU l3) → is-equiv (ev-suspension susp-str-Y Z)
is-equiv-ev-suspension {X = X} susp-str-Y up-Y Z =
  is-equiv-comp
    ( ev-suspension susp-str-Y Z)
    ( map-comparison-suspension-cocone X Z)
    ( cocone-map
      ( const X unit star)
      ( const X unit star)
      ( cocone-suspension-structure X _ susp-str-Y))
    ( inv-htpy (triangle-ev-suspension susp-str-Y Z))
    ( up-Y Z)
    ( is-equiv-map-comparison-suspension-cocone X Z)
```

### The suspension of a contractible type is contractible

```agda
is-contr-suspension-is-contr :
  {l : Level} {X : UU l} → is-contr X → is-contr (suspension X)
is-contr-suspension-is-contr {l} {X} is-contr-X =
  is-contr-is-equiv'
    ( unit)
    ( pr1 (pr2 (cocone-pushout (const X unit star) (const X unit star))))
    ( is-equiv-universal-property-pushout
      ( const X unit star)
      ( const X unit star)
      ( cocone-pushout
        ( const X unit star)
        ( const X unit star))
      ( is-equiv-is-contr (const X unit star) is-contr-X is-contr-unit)
      ( up-pushout (const X unit star) (const X unit star)))
    ( is-contr-unit)
```

### The suspension of X has the universal proprety of suspensions

```agda
module _
  {l1 : Level} (X : UU l1)
  where
  
  up-suspension :
    {l : Level} → universal-property-suspension l X  (suspension X) (N-susp , S-susp , merid-susp)
  up-suspension Z = htpy-preserve-is-equiv ((pr2 ( (comparison-suspension-cocone X Z) ∘e
    (equiv-up-pushout (const X unit star) (const X unit star) Z))))
    ((triangle-ev-suspension {X = X} {Y = suspension X} (N-susp , S-susp , merid-susp) Z)) 

  equiv-up-suspension :
    {l : Level} (Z : UU l) → ((suspension X) → Z) ≃ (suspension-cocone X Z)
  equiv-up-suspension Z = (ev-suspension (N-susp , S-susp , merid-susp) Z) , up-suspension Z  

  map-inv-up-suspension : {l : Level} (Z : UU l) →
    (suspension-cocone X Z) → ((suspension X) → Z)
  map-inv-up-suspension Z = map-inv-equiv (equiv-up-suspension Z)

  issec-map-inv-up-suspension : {l : Level} (Z : UU l) →
    ((ev-suspension (susp-struct X) Z) ∘ (map-inv-up-suspension Z)) ~ id
  issec-map-inv-up-suspension Z = issec-map-inv-is-equiv (up-suspension Z)

  isretr-map-inv-up-suspension : {l : Level} (Z : UU l) →
    ((map-inv-up-suspension Z) ∘ (ev-suspension (susp-struct X) Z)) ~ id
  isretr-map-inv-up-suspension Z = isretr-map-inv-is-equiv (up-suspension Z)

  up-suspension-N-susp : {l : Level} (Z : UU l) (c : suspension-cocone X Z) →
    (map-inv-up-suspension Z c N-susp) ＝ pr1 c 
  up-suspension-N-susp Z c = {!ap (pr1) (((issec-map-inv-up-suspension Z) c))!}
```
