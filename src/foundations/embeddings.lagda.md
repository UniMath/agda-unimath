---
title: Univalent Mathematics in Agda
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundations.embeddings where

open import foundations.contractible-maps using (is-contr-map-is-equiv)
open import foundations.contractible-types using
  ( is-contr-equiv; is-contr-total-path)
open import foundations.coproduct-types using (coprod; inl; inr)
open import foundations.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundations.empty-type using (ex-falso; empty)
open import foundations.equality-coproduct-types using
  ( compute-eq-coprod-inl-inl; compute-eq-coprod-inr-inr)
open import foundations.equivalences using
  ( is-equiv; _≃_; map-inv-is-equiv; equiv-inv; map-equiv; is-equiv-map-equiv;
    id-equiv)
open import foundations.fibers-of-maps using (fib)
open import foundations.functions using (id)
open import foundations.functoriality-dependent-pair-types using (equiv-tot)
open import foundations.fundamental-theorem-of-identity-types using
  ( fundamental-theorem-id)
open import foundations.injective-maps using (is-injective)
open import foundations.levels using (Level; UU; _⊔_)
open import foundations.identity-types using (Id; refl; ap)
```

# Embeddings

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-emb : (A → B) → UU (l1 ⊔ l2)
  is-emb f = (x y : A) → is-equiv (ap f {x} {y})

_↪_ :
  {l1 l2 : Level} → UU l1 → UU l2 → UU (l1 ⊔ l2)
A ↪ B = Σ (A → B) is-emb

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  map-emb : A ↪ B → A → B
  map-emb f = pr1 f

  is-emb-map-emb : (f : A ↪ B) → is-emb (map-emb f)
  is-emb-map-emb f = pr2 f

  equiv-ap-emb : (e : A ↪ B) {x y : A} → Id x y ≃ Id (map-emb e x) (map-emb e y)
  pr1 (equiv-ap-emb e {x} {y}) = ap (map-emb e)
  pr2 (equiv-ap-emb e {x} {y}) = is-emb-map-emb e x y

  is-injective-is-emb : {f : A → B} → is-emb f → is-injective f
  is-injective-is-emb is-emb-f {x} {y} = map-inv-is-equiv (is-emb-f x y)

  is-injective-emb : (e : A ↪ B) → is-injective (map-emb e)
  is-injective-emb e {x} {y} = map-inv-is-equiv (is-emb-map-emb e x y)

  is-emb-is-equiv : {f : A → B} → is-equiv f → is-emb f
  is-emb-is-equiv {f} is-equiv-f x =
    fundamental-theorem-id x refl
      ( is-contr-equiv
        ( fib f (f x))
        ( equiv-tot (λ y → equiv-inv (f x) (f y)))
        ( is-contr-map-is-equiv is-equiv-f (f x)))
      ( λ y p → ap f p)

  emb-equiv : (A ≃ B) → (A ↪ B)
  pr1 (emb-equiv e) = map-equiv e
  pr2 (emb-equiv e) = is-emb-is-equiv (is-equiv-map-equiv e)

  equiv-ap :
    (e : A ≃ B) (x y : A) → (Id x y) ≃ (Id (map-equiv e x) (map-equiv e y))
  pr1 (equiv-ap e x y) = ap (map-equiv e) {x} {y}
  pr2 (equiv-ap e x y) = is-emb-is-equiv (is-equiv-map-equiv e) x y

module _
  {l : Level} {A : UU l}
  where

  id-emb : A ↪ A
  id-emb = emb-equiv id-equiv

  is-emb-id : is-emb (id {A = A})
  is-emb-id = is-emb-map-emb id-emb
```

## The map `ex-falso` is an embedding

```agda
module _
  {l : Level} {A : UU l}
  where
  
  abstract
    is-emb-ex-falso : is-emb (ex-falso {A = A})
    is-emb-ex-falso ()

  ex-falso-emb : empty ↪ A
  pr1 ex-falso-emb = ex-falso
  pr2 ex-falso-emb = is-emb-ex-falso
```

## The left and right inclusions into a coproduct are embeddings

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where
  
  abstract
    is-emb-inl : is-emb (inl {A = A} {B = B})
    is-emb-inl x =
      fundamental-theorem-id x refl
        ( is-contr-equiv
          ( Σ A (Id x))
          ( equiv-tot (compute-eq-coprod-inl-inl x))
          ( is-contr-total-path x))
        ( λ y → ap inl)

  emb-inl : A ↪ coprod A B
  pr1 emb-inl = inl
  pr2 emb-inl = is-emb-inl

  abstract
    is-emb-inr : is-emb (inr {A = A} {B = B})
    is-emb-inr x =
      fundamental-theorem-id x refl
        ( is-contr-equiv
          ( Σ B (Id x))
          ( equiv-tot (compute-eq-coprod-inr-inr x))
          ( is-contr-total-path x))
        ( λ y → ap inr)

  emb-inr : B ↪ coprod A B
  pr1 emb-inr = inr
  pr2 emb-inr = is-emb-inr
```

