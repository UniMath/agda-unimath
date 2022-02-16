# Subuniverse

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.subuniverses where

open import foundation-core.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation-core.equivalences using
  ( _≃_; id-equiv; is-equiv; map-inv-is-equiv)
open import foundation-core.fundamental-theorem-of-identity-types using
  ( fundamental-theorem-id)
open import foundation-core.identity-types using (Id; tr; inv; refl; ap)
open import foundation-core.propositions using
  ( is-prop; type-Prop; is-prop-type-Prop; UU-Prop)
open import foundation-core.sets using (is-set; UU-Set)
open import foundation-core.subtype-identity-principle using
  ( is-contr-total-Eq-subtype)
open import foundation-core.subtypes using (is-subtype; subtype; is-emb-pr1)
open import foundation-core.universe-levels using (Level; UU; lsuc; _⊔_)

open import foundation.contractible-types using
  ( is-contr; is-contr-Prop; equiv-is-contr)
open import foundation.truncated-types using
  ( is-trunc; is-trunc-is-equiv; is-prop-is-trunc; is-trunc-equiv-is-trunc)
open import foundation.truncation-levels using
  ( 𝕋; neg-two-𝕋; succ-𝕋; neg-one-𝕋)
open import foundation.unit-type using (raise-unit; is-contr-raise-unit)
open import foundation.univalence using
  ( eq-equiv; is-contr-total-equiv; equiv-eq; univalence)
```

## Idea

Subuniverses are subtypes of the universe.

```agda
is-subuniverse :
  {l1 l2 : Level} (P : UU l1 → UU l2) → UU ((lsuc l1) ⊔ l2)
is-subuniverse P = is-subtype P

subuniverse :
  (l1 l2 : Level) → UU ((lsuc l1) ⊔ (lsuc l2))
subuniverse l1 l2 = subtype l2 (UU l1)

abstract
  is-subtype-subuniverse :
    {l1 l2 : Level} (P : subuniverse l1 l2) (X : UU l1) →
    is-prop (type-Prop (P X))
  is-subtype-subuniverse P X = is-prop-type-Prop (P X)

{- By univalence, subuniverses are closed under equivalences. -}
in-subuniverse-equiv :
  {l1 l2 : Level} (P : UU l1 → UU l2) {X Y : UU l1} → X ≃ Y → P X → P Y
in-subuniverse-equiv P e = tr P (eq-equiv _ _ e)

in-subuniverse-equiv' :
  {l1 l2 : Level} (P : UU l1 → UU l2) {X Y : UU l1} → X ≃ Y → P Y → P X
in-subuniverse-equiv' P e = tr P (inv (eq-equiv _ _ e))

total-subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2) → UU ((lsuc l1) ⊔ l2)
total-subuniverse {l1} P = Σ (UU l1) (λ X → type-Prop (P X))

{- We also introduce the notion of 'global subuniverse'. The handling of 
   universe levels is a bit more complicated here, since (l : Level) → A l are 
   kinds but not types. -}
   
is-global-subuniverse :
  (α : Level → Level) (P : (l : Level) → subuniverse l (α l)) →
  (l1 l2 : Level) → UU _
is-global-subuniverse α P l1 l2 =
  (X : UU l1) (Y : UU l2) → X ≃ Y → type-Prop (P l1 X) → type-Prop (P l2 Y)

{- Next we characterize the identity type of a subuniverse. -}

equiv-subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2) →
  (X Y : total-subuniverse P) → UU l1
equiv-subuniverse P X Y = (pr1 X) ≃ (pr1 Y)

equiv-eq-subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2) →
  (s t : total-subuniverse P) → Id s t → equiv-subuniverse P s t
equiv-eq-subuniverse P (pair X p) .(pair X p) refl = id-equiv

abstract
  is-contr-total-equiv-subuniverse :
    {l1 l2 : Level} (P : subuniverse l1 l2)
    (s : total-subuniverse P) →
    is-contr (Σ (total-subuniverse P) (λ t → equiv-subuniverse P s t))
  is-contr-total-equiv-subuniverse P (pair X p) =
    is-contr-total-Eq-subtype
      ( is-contr-total-equiv X)
      ( is-subtype-subuniverse P)
      ( X)
      ( id-equiv)
      ( p)

abstract
  is-equiv-equiv-eq-subuniverse :
    {l1 l2 : Level} (P : subuniverse l1 l2)
    (s t : total-subuniverse P) → is-equiv (equiv-eq-subuniverse P s t)
  is-equiv-equiv-eq-subuniverse P (pair X p) =
    fundamental-theorem-id
      ( pair X p)
      ( id-equiv)
      ( is-contr-total-equiv-subuniverse P (pair X p))
      ( equiv-eq-subuniverse P (pair X p))

eq-equiv-subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2) →
  {s t : total-subuniverse P} → equiv-subuniverse P s t → Id s t
eq-equiv-subuniverse P {s} {t} =
  map-inv-is-equiv (is-equiv-equiv-eq-subuniverse P s t)
```

```agda
UU-Contr : (l : Level) → UU (lsuc l)
UU-Contr l = total-subuniverse is-contr-Prop

type-UU-Contr : {l : Level} → UU-Contr l → UU l
type-UU-Contr A = pr1 A

abstract
  is-contr-type-UU-Contr :
    {l : Level} (A : UU-Contr l) → is-contr (type-UU-Contr A)
  is-contr-type-UU-Contr A = pr2 A

equiv-UU-Contr :
  {l1 l2 : Level} (X : UU-Contr l1) (Y : UU-Contr l2) → UU (l1 ⊔ l2)
equiv-UU-Contr X Y = type-UU-Contr X ≃ type-UU-Contr Y

equiv-eq-UU-Contr :
  {l1 : Level} (X Y : UU-Contr l1) → Id X Y → equiv-UU-Contr X Y
equiv-eq-UU-Contr X Y = equiv-eq-subuniverse is-contr-Prop X Y

abstract
  is-equiv-equiv-eq-UU-Contr :
    {l1 : Level} (X Y : UU-Contr l1) → is-equiv (equiv-eq-UU-Contr X Y)
  is-equiv-equiv-eq-UU-Contr X Y =
    is-equiv-equiv-eq-subuniverse is-contr-Prop X Y

eq-equiv-UU-Contr :
  {l1 : Level} {X Y : UU-Contr l1} → equiv-UU-Contr X Y → Id X Y
eq-equiv-UU-Contr = eq-equiv-subuniverse is-contr-Prop

abstract
  center-UU-contr : (l : Level) → UU-Contr l
  center-UU-contr l = pair (raise-unit l) is-contr-raise-unit
  
  contraction-UU-contr :
    {l : Level} (A : UU-Contr l) → Id (center-UU-contr l) A
  contraction-UU-contr A =
    eq-equiv-UU-Contr
      ( equiv-is-contr is-contr-raise-unit (is-contr-type-UU-Contr A))

abstract
  is-contr-UU-Contr : (l : Level) → is-contr (UU-Contr l)
  is-contr-UU-Contr l = pair (center-UU-contr l) contraction-UU-contr
```

```agda
UU-Trunc : (k : 𝕋) (l : Level) → UU (lsuc l)
UU-Trunc k l = Σ (UU l) (is-trunc k)

type-UU-Trunc : {k : 𝕋} {l : Level} → UU-Trunc k l → UU l
type-UU-Trunc A = pr1 A

abstract
  is-trunc-type-UU-Trunc :
    {k : 𝕋} {l : Level} (A : UU-Trunc k l) → is-trunc k (type-UU-Trunc A)
  is-trunc-type-UU-Trunc A = pr2 A

abstract
  is-trunc-UU-Trunc :
    (k : 𝕋) (l : Level) → is-trunc (succ-𝕋 k) (UU-Trunc k l)
  is-trunc-UU-Trunc k l X Y =
    is-trunc-is-equiv k
      ( Id (pr1 X) (pr1 Y))
      ( ap pr1)
      ( is-emb-pr1
        ( is-prop-is-trunc k) X Y)
      ( is-trunc-is-equiv k
        ( (pr1 X) ≃ (pr1 Y))
        ( equiv-eq)
        ( univalence (pr1 X) (pr1 Y))
        ( is-trunc-equiv-is-trunc k (pr2 X) (pr2 Y)))

abstract
  is-set-UU-Prop : (l : Level) → is-set (UU-Prop l)
  is-set-UU-Prop l = is-trunc-UU-Trunc (neg-one-𝕋) l

UU-Prop-Set : (l : Level) → UU-Set (lsuc l)
UU-Prop-Set l = pair (UU-Prop l) (is-set-UU-Prop l)
```
