# Identity systems

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundation.identity-systems where

open import foundation.contractible-types using
  ( is-contr; eq-is-contr; eq-is-contr')
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2; fam-Σ)
open import foundation.equivalences using (sec; is-equiv)
open import foundation.fundamental-theorem-of-identity-types using
  ( fundamental-theorem-id)
open import foundation.identity-types using (tr; ap; refl; Id)
open import foundation.propositions using (is-prop-is-contr)
open import foundation.universe-levels using (Level; UU; lsuc; _⊔_)
```

## Idea

A unary identity system on a type `A` equipped with a point `a : A` consists of a type family `B` over `A` equipped with a point `b : B a` that satisfies an induction principle analogous to the induction principle of the identity type at `a`.

```agda
module _
  {l1 l2 : Level} (l : Level) {A : UU l1} (B : A → UU l2) (a : A) (b : B a)
  where

  IND-identity-system : UU (l1 ⊔ l2 ⊔ lsuc l)
  IND-identity-system =
    ( P : (x : A) (y : B x) → UU l) →
      sec (λ (h : (x : A) (y : B x) → P x y) → h a b)
```

## Properties

### A type family over `A` is an identity system if and only if it is equivalent to the identity type

```
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (a : A) (b : B a)
  where

  abstract
    Ind-identity-system :
      (is-contr-AB : is-contr (Σ A B)) →
      {l : Level} → IND-identity-system l B a b
    pr1 (Ind-identity-system is-contr-AB P) p x y =
      tr ( fam-Σ P)
         ( eq-is-contr is-contr-AB)
         ( p)
    pr2 (Ind-identity-system is-contr-AB P) p =
      ap ( λ t → tr (fam-Σ P) t p)
         ( eq-is-contr'
           ( is-prop-is-contr is-contr-AB (pair a b) (pair a b))
           ( eq-is-contr is-contr-AB)
           ( refl))

  abstract
    is-contr-total-space-IND-identity-system :
      ({l : Level} → IND-identity-system l B a b) → is-contr (Σ A B)
    pr1 (pr1 (is-contr-total-space-IND-identity-system ind)) = a
    pr2 (pr1 (is-contr-total-space-IND-identity-system ind)) = b
    pr2 (is-contr-total-space-IND-identity-system ind) (pair x y) =
      pr1 (ind (λ x' y' → Id (pair a b) (pair x' y'))) refl x y

  abstract
    fundamental-theorem-id-IND-identity-system :
      ({l : Level} → IND-identity-system l B a b) →
      (f : (x : A) → Id a x → B x) → (x : A) → is-equiv (f x)
    fundamental-theorem-id-IND-identity-system ind f =
      fundamental-theorem-id a b
        ( is-contr-total-space-IND-identity-system ind)
        ( f)
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where
  
  abstract
    Ind-htpy-equiv :
      {l3 : Level} (e : A ≃ B)
      (P : (e' : A ≃ B) (H : htpy-equiv e e') → UU l3) →
      sec ( λ (h : (e' : A ≃ B) (H : htpy-equiv e e') → P e' H) →
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
