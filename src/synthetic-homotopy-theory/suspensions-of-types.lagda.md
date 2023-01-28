---
title: Suspensions of types
---

```agda
module synthetic-homotopy-theory.suspensions-of-types where

open import foundation.constant-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.functions
open import foundation.function-extensionality
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
suspension-structure X Y = Σ Y (λ N → Σ Y (λ S → (x : X) → N ＝ S))

suspension-structure-N :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → (suspension-structure X Y) → Y
suspension-structure-N c = pr1 c

suspension-structure-S :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → (suspension-structure X Y) → Y
suspension-structure-S c = (pr1 ∘ pr2) c

suspension-structure-merid :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (c : suspension-structure X Y) → X → ((suspension-structure-N c) ＝ (suspension-structure-S c))
suspension-structure-merid c = (pr2 ∘ pr2) c

suspension-cocone :
  {l1 l2 : Level} (X : UU l1) (Y : UU l2) → UU (l1 ⊔ l2)
suspension-cocone X Y = cocone (const X unit star) (const X unit star) Y

cocone-suspension-structure :
  {l1 l2 : Level} (X : UU l1) (Y : UU l2) →
  suspension-structure X Y → suspension-cocone X Y
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

suspension-structure-suspension :
  {l : Level} (X : UU l) → suspension-structure X (suspension X)
pr1 (suspension-structure-suspension X) = N-susp
pr1 (pr2 (suspension-structure-suspension X)) = S-susp
pr2 (pr2 (suspension-structure-suspension X)) = merid-susp
```

## Properties

### The universal property of the suspension as a pushout

```agda
ev-suspension :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} →
  (susp-str-Y : suspension-structure X Y) →
  (Z : UU l3) → (Y → Z) → suspension-structure X Z
ev-suspension (pair N (pair S merid)) Z h =
  pair (h N) (pair (h S) (h ·l merid))

universal-property-suspension :
  (l : Level) {l1 l2 : Level} (X : UU l1) (Y : UU l2) →
  suspension-structure X Y → UU (lsuc l ⊔ l1 ⊔ l2)
universal-property-suspension l X Y susp-str-Y =
  (Z : UU l) → is-equiv (ev-suspension susp-str-Y Z)

comparison-suspension-cocone :
  {l1 l2 : Level} (X : UU l1) (Z : UU l2) →
  suspension-cocone X Z ≃ suspension-structure X Z
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
  suspension-cocone X Z → suspension-structure X Z
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

#### Characterization of equalities in `suspension-structure`

```agda
suspension-structure-htpy : {l1 l2 : Level} {X : UU l1} {Z : UU l2} 
  (c c' : suspension-structure X Z) → UU (l1 ⊔ l2)
suspension-structure-htpy {X = X} c c' =
  Σ ((suspension-structure-N c) ＝ (suspension-structure-N c'))
  (λ p → Σ ((suspension-structure-S c) ＝ (suspension-structure-S c'))
  (λ q → (x : X) → (((inv p) ∙ (suspension-structure-merid c x)) ∙ q)
  ＝ (suspension-structure-merid c' x)))

suspension-structure-eq-suspension-structure-htpy :
  {l1 l2 : Level} {X : UU l1} {Z : UU l2} (c c' : suspension-structure X Z) →
  (suspension-structure-htpy c c') → c ＝ c'
suspension-structure-eq-suspension-structure-htpy
  (N , S , h) (N' , S' , h') (refl , refl , H) =
  eq-pair-Σ refl (eq-pair-Σ refl
  (eq-htpy (λ x → (inv right-unit) ∙ H x)))

merid-htpy-cocone-eq :
  {l1 l2 : Level} {X : UU l1} {Z : UU l2} (c c' : suspension-structure X Z) →
  (p : c ＝ c') → (x : X) → ((inv (ap pr1 p) ∙ (suspension-structure-merid c x)) ∙
  ap (pr1 ∘ pr2) p) ＝ (suspension-structure-merid c' x)
merid-htpy-cocone-eq {X = X} c c' p x = ((inv (tr-fx＝gx (pr1) (pr1 ∘ pr2) p ((pr2 ∘ pr2) c x)) ∙
  (ap (λ t → tr (λ z → pr1 z ＝ (pr1 ∘ pr2) z) p ((pr2 ∘ pr2) c t))
  (inv (tr-const (inv p) x)))) ∙
  inv (htpy-eq (tr-function-type
  (λ z → X) (λ z → (pr1 z) ＝ ((pr1 ∘ pr2) z))
  p  ((pr2 ∘ pr2) c)) x)) ∙ (htpy-eq (apd (pr2 ∘ pr2) p) x)
  
suspension-structure-htpy-suspension-structure-eq :
  {l1 l2 : Level} {X : UU l1} {Z : UU l2} (c c' : suspension-structure X Z) →
  (c ＝ c') → (suspension-structure-htpy c c')
suspension-structure-htpy-suspension-structure-eq
  c c' p = (ap pr1 p) , ((ap (pr1 ∘ pr2) p) , merid-htpy-cocone-eq c c' p)

issec-suspension-structure-htpy-suspension-structure-eq :
  {l1 l2 : Level} {X : UU l1} {Z : UU l2} 
  (c c' : suspension-structure X Z) →
  ((suspension-structure-eq-suspension-structure-htpy c c') ∘
  (suspension-structure-htpy-suspension-structure-eq c c')) ~ id
issec-suspension-structure-htpy-suspension-structure-eq (N , S , h) (N' , S' , h') refl =
    (ap (λ t → eq-pair-Σ refl (eq-pair-Σ refl (eq-htpy t)))
    (eq-htpy λ x → (ap-binary (_∙_)(refl{x = inv right-unit})
    ((right-unit ∙ right-unit) ∙ right-unit)) ∙
    (right-inv (inv right-unit)) ) ∙
    ap (λ t → eq-pair-Σ refl (eq-pair-Σ refl t))
    (eq-htpy-refl-htpy h))
```

### The suspension of X has the universal proprety of suspensions

```agda
module _
  {l1 : Level} (X : UU l1)
  where

  up-suspension :
    {l : Level} →
    universal-property-suspension l X
      ( suspension X)
      ( suspension-structure-suspension X)
  up-suspension Z =
    is-equiv-htpy
      ( ev-suspension (suspension-structure-suspension X) Z)
      ( triangle-ev-suspension
        { X = X}
        { Y = suspension X}
        ( suspension-structure-suspension X) Z)
      ( is-equiv-map-equiv
        ( ( comparison-suspension-cocone X Z) ∘e
          ( equiv-up-pushout (const X unit star) (const X unit star) Z)))

  equiv-up-suspension :
    {l : Level} (Z : UU l) → ((suspension X) → Z) ≃ (suspension-structure X Z)
  equiv-up-suspension Z = (ev-suspension (suspension-structure-suspension X) Z) , up-suspension Z

  map-inv-up-suspension : {l : Level} (Z : UU l) →
    (suspension-structure X Z) → ((suspension X) → Z)
  map-inv-up-suspension Z =
    map-inv-equiv (equiv-up-suspension Z)

  issec-map-inv-up-suspension :
    {l : Level} (Z : UU l) →
    ((ev-suspension ((suspension-structure-suspension X)) Z) ∘
    (map-inv-up-suspension Z)) ~ id
  issec-map-inv-up-suspension Z = issec-map-inv-is-equiv (up-suspension Z)

  isretr-map-inv-up-suspension : {l : Level} (Z : UU l) →
    ((map-inv-up-suspension Z) ∘ (ev-suspension ((suspension-structure-suspension X)) Z)) ~ id
  isretr-map-inv-up-suspension Z = isretr-map-inv-is-equiv (up-suspension Z)

  up-suspension-N-susp :
    {l : Level} (Z : UU l) (c : suspension-structure X Z) →
    (map-inv-up-suspension Z c N-susp) ＝ pr1 c 
  up-suspension-N-susp Z c =
    pr1 (suspension-structure-htpy-suspension-structure-eq
    (ev-suspension (suspension-structure-suspension X) Z
    (map-inv-up-suspension Z c)) c ((issec-map-inv-up-suspension Z) c))

  up-suspension-S-susp : {l : Level} (Z : UU l) (c : suspension-structure X Z) →
    (map-inv-up-suspension Z c S-susp) ＝ pr1 (pr2 c)
  up-suspension-S-susp Z c = pr1 (pr2 (suspension-structure-htpy-suspension-structure-eq
    (ev-suspension (suspension-structure-suspension X) Z
    (map-inv-up-suspension Z c)) c ((issec-map-inv-up-suspension Z) c)))

  up-suspension-merid-susp : {l : Level} (Z : UU l) (c : suspension-structure X Z) (x : X) →
    (((inv (up-suspension-N-susp Z c) ∙ (ap (map-inv-up-suspension Z c) (merid-susp x))) ∙
    (up-suspension-S-susp Z c)) ＝ (pr2 (pr2 c)) x)
  up-suspension-merid-susp Z c = pr2 (pr2 (suspension-structure-htpy-suspension-structure-eq
    (ev-suspension (suspension-structure-suspension X) Z
    (map-inv-up-suspension Z c)) c ((issec-map-inv-up-suspension Z) c)))

  ev-suspension-up-suspension :
    {l : Level} (Z : UU l) (c : suspension-structure X Z) →
    (ev-suspension (suspension-structure-suspension X) Z (map-inv-up-suspension Z c)) ＝ c
  ev-suspension-up-suspension Z c =
    suspension-structure-eq-suspension-structure-htpy
    (ev-suspension (suspension-structure-suspension X) Z
    (map-inv-up-suspension Z c)) c ((up-suspension-N-susp Z c) ,
    ((up-suspension-S-susp Z c) , (up-suspension-merid-susp Z c)))
```
