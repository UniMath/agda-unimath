# Subuniverse

```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module foundation.subuniverses where

open import foundation.contractible-types using (is-contr)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using
  ( _≃_; id-equiv; is-equiv; map-inv-is-equiv)
open import foundation.fundamental-theorem-of-identity-types using
  ( fundamental-theorem-id)
open import foundation.identity-types using (Id; tr; inv; refl)
open import foundation.propositions using
  ( is-prop; type-Prop; is-prop-type-Prop)
open import foundation.subtype-identity-principle using
  ( is-contr-total-Eq-subtype)
open import foundation.subtypes using (is-subtype; subtype)
open import foundation.univalence using (eq-equiv; is-contr-total-equiv)
open import foundation.universe-levels using (Level; UU; lsuc; _⊔_)
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
