# Function extensionality

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.homotopy-induction where

open import foundation.contractible-types using (is-contr)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using
  ( _≃_; map-equiv; is-equiv; map-inv-is-equiv)
open import foundation.foundation-base using ([sec])
open import foundation.function-extensionality using
  ( FUNEXT; htpy-eq; funext)
open import foundation.fundamental-theorem-of-identity-types using
  ( is-contr-total-htpy; fundamental-theorem-id)
open import foundation.equivalences-with-function-extensionality using
  ( is-subtype-is-equiv; htpy-equiv; refl-htpy-equiv; is-contr-total-htpy-equiv)
open import foundation.homotopies using (_~_; refl-htpy)
open import foundation.identity-systems using
  ( Ind-identity-system; fundamental-theorem-id-IND-identity-system)
open import foundation.identity-types using (Id; refl)
open import foundation.subtype-identity-principle using
  ( is-contr-total-Eq-subtype)
open import foundation.universe-levels using (Level; UU; _⊔_)
```

### Homotopy induction

```agda
ev-refl-htpy :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) (C : (g : (x : A) → B x) → (f ~ g) → UU l3) →
  ((g : (x : A) → B x) (H : f ~ g) → C g H) → C f refl-htpy
ev-refl-htpy f C φ = φ f refl-htpy

IND-HTPY :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) → UU _
IND-HTPY {l1} {l2} {l3} {A} {B} f =
  (C : (g : (x : A) → B x) → (f ~ g) → UU l3) → [sec] (ev-refl-htpy f C)
```

## Properties

```agda
abstract
  IND-HTPY-FUNEXT :
    {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (f : (x : A) → B x) →
    FUNEXT f → IND-HTPY {l3 = l3} f
  IND-HTPY-FUNEXT {l3 = l3} {A = A} {B = B} f funext-f =
    Ind-identity-system f
      ( refl-htpy)
      ( is-contr-total-htpy f)

abstract
  FUNEXT-IND-HTPY :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (f : (x : A) → B x) →
    ({l : Level} → IND-HTPY {l3 = l} f) → FUNEXT f
  FUNEXT-IND-HTPY f ind-htpy-f =
    fundamental-theorem-id-IND-identity-system f
      ( refl-htpy)
      ( ind-htpy-f)
      ( λ g → htpy-eq)
```

```agda
abstract
  Ind-htpy :
    {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (f : (x : A) → B x) →
    IND-HTPY {l3 = l3} f
  Ind-htpy f = IND-HTPY-FUNEXT f (funext f)
  
  ind-htpy :
    {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
    (f : (x : A) → B x) (C : (g : (x : A) → B x) → (f ~ g) → UU l3) →
    C f refl-htpy → {g : (x : A) → B x} (H : f ~ g) → C g H
  ind-htpy f C t {g} = pr1 (Ind-htpy f C) t g
  
  comp-htpy :
    {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
    (f : (x : A) → B x) (C : (g : (x : A) → B x) → (f ~ g) → UU l3) →
    (c : C f refl-htpy) →
    Id (ind-htpy f C c refl-htpy) c
  comp-htpy f C = pr2 (Ind-htpy f C)
```

### Homotopy induction for homotopies between equivalences

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where
  
  abstract
    Ind-htpy-equiv :
      {l3 : Level} (e : A ≃ B)
      (P : (e' : A ≃ B) (H : htpy-equiv e e') → UU l3) →
      [sec]
        ( λ (h : (e' : A ≃ B) (H : htpy-equiv e e') → P e' H) →
          h e (refl-htpy-equiv e))
    Ind-htpy-equiv e =
      Ind-identity-system e
        ( refl-htpy-equiv e)
        ( is-contr-total-htpy-equiv e)
  
  ind-htpy-equiv :
    {l3 : Level} (e : A ≃ B) (P : (e' : A ≃ B) (H : htpy-equiv e e') → UU l3) →
    P e (refl-htpy-equiv e) → (e' : A ≃ B) (H : htpy-equiv e e') → P e' H
  ind-htpy-equiv e P = pr1 (Ind-htpy-equiv e P)
  
  comp-htpy-equiv :
    {l3 : Level} (e : A ≃ B) (P : (e' : A ≃ B) (H : htpy-equiv e e') → UU l3)
    (p : P e (refl-htpy-equiv e)) →
    Id (ind-htpy-equiv e P p e (refl-htpy-equiv e)) p
  comp-htpy-equiv e P = pr2 (Ind-htpy-equiv e P)
```
