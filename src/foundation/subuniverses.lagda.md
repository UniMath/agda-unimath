---
title: Subuniverse
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.subuniverses where

open import foundation-core.contractible-types using
  ( is-contr)
open import foundation-core.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation-core.equivalences using
  ( _≃_; id-equiv; is-equiv; map-inv-is-equiv)
open import foundation-core.fundamental-theorem-of-identity-types using
  ( fundamental-theorem-id)
open import foundation-core.identity-types using (_＝_; tr; inv; refl; ap)
open import foundation-core.propositions using
  ( is-prop; type-Prop; is-prop-type-Prop; UU-Prop)
open import foundation-core.sets using (is-set; UU-Set)
open import foundation-core.subtype-identity-principle using
  ( is-contr-total-Eq-subtype)
open import foundation-core.subtypes using
  ( is-subtype; subtype; is-emb-inclusion-subtype)
open import foundation-core.univalence using
  ( eq-equiv; is-contr-total-equiv; equiv-eq)
open import foundation-core.universe-levels using (Level; UU; lsuc; _⊔_)

open import foundation.equality-dependent-function-types
open import foundation.unit-type using (raise-unit; is-contr-raise-unit)
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
  (s t : total-subuniverse P) → s ＝ t → equiv-subuniverse P s t
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
      ( is-contr-total-equiv-subuniverse P (pair X p))
      ( equiv-eq-subuniverse P (pair X p))

extensionality-subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2) (s t : total-subuniverse P) →
  (s ＝ t) ≃ equiv-subuniverse P s t
pr1 (extensionality-subuniverse P s t) = equiv-eq-subuniverse P s t
pr2 (extensionality-subuniverse P s t) = is-equiv-equiv-eq-subuniverse P s t

eq-equiv-subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2) →
  {s t : total-subuniverse P} → equiv-subuniverse P s t → s ＝ t
eq-equiv-subuniverse P {s} {t} =
  map-inv-is-equiv (is-equiv-equiv-eq-subuniverse P s t)
```

### Equivalences of families of types in a subuniverse

```agda
fam-subuniverse :
  {l1 l2 l3 : Level} (P : subuniverse l1 l2) (X : UU l3) →
  UU (lsuc l1 ⊔ l2 ⊔ l3)
fam-subuniverse P X = X → total-subuniverse P

module _
  {l1 l2 l3 : Level} (P : subuniverse l1 l2) {X : UU l3}
  where
  
  equiv-fam-subuniverse :
    (Y Z : fam-subuniverse P X) → UU (l1 ⊔ l3)
  equiv-fam-subuniverse Y Z = (x : X) → equiv-subuniverse P (Y x) (Z x)

  id-equiv-fam-subuniverse :
    (Y : fam-subuniverse P X) → equiv-fam-subuniverse Y Y
  id-equiv-fam-subuniverse Y x = id-equiv

  is-contr-total-equiv-fam-subuniverse :
    (Y : fam-subuniverse P X) →
    is-contr (Σ (fam-subuniverse P X) (equiv-fam-subuniverse Y))
  is-contr-total-equiv-fam-subuniverse Y =
    is-contr-total-Eq-Π
      ( λ x → equiv-subuniverse P (Y x))
      ( λ x → is-contr-total-equiv-subuniverse P (Y x))

  equiv-eq-fam-subuniverse :
    (Y Z : fam-subuniverse P X) → Y ＝ Z → equiv-fam-subuniverse Y Z
  equiv-eq-fam-subuniverse Y .Y refl = id-equiv-fam-subuniverse Y

  is-equiv-equiv-eq-fam-subuniverse :
    (Y Z : fam-subuniverse P X) → is-equiv (equiv-eq-fam-subuniverse Y Z)
  is-equiv-equiv-eq-fam-subuniverse Y =
    fundamental-theorem-id 
      ( is-contr-total-equiv-fam-subuniverse Y)
      ( equiv-eq-fam-subuniverse Y)

  extensionality-fam-subuniverse :
    (Y Z : fam-subuniverse P X) → (Y ＝ Z) ≃ equiv-fam-subuniverse Y Z
  pr1 (extensionality-fam-subuniverse Y Z) = equiv-eq-fam-subuniverse Y Z
  pr2 (extensionality-fam-subuniverse Y Z) =
    is-equiv-equiv-eq-fam-subuniverse Y Z

  eq-equiv-fam-subuniverse :
    (Y Z : fam-subuniverse P X) → equiv-fam-subuniverse Y Z → (Y ＝ Z)
  eq-equiv-fam-subuniverse Y Z =
    map-inv-is-equiv (is-equiv-equiv-eq-fam-subuniverse Y Z)
```
