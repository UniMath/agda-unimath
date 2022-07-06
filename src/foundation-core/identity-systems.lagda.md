---
title: Identity systems
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation-core.identity-systems where

open import foundation-core.contractible-types using
  ( is-contr; eq-is-contr; eq-is-contr'; is-prop-is-contr)
open import foundation-core.dependent-pair-types using (Σ; pair; pr1; pr2; fam-Σ)
open import foundation-core.equivalences using (is-equiv; _≃_)
open import foundation-core.fundamental-theorem-of-identity-types using
  ( fundamental-theorem-id)
open import foundation-core.identity-types using (tr; ap; refl; _＝_)
open import foundation-core.sections using (sec)
open import foundation-core.universe-levels using (Level; UU; lsuc; _⊔_)
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
      pr1 (ind (λ x' y' → (pair a b) ＝ (pair x' y'))) refl x y

  abstract
    fundamental-theorem-id-IND-identity-system :
      ({l : Level} → IND-identity-system l B a b) →
      (f : (x : A) → a ＝ x → B x) → (x : A) → is-equiv (f x)
    fundamental-theorem-id-IND-identity-system ind f =
      fundamental-theorem-id a b
        ( is-contr-total-space-IND-identity-system ind)
        ( f)
```
