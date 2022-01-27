---
title: Univalent Mathematics in Agda
---

# Subtypes

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundation.subtypes where

open import foundation.1-types using (is-1-type)
open import foundation.contractible-types using
  ( is-contr; is-contr-equiv; is-contr-total-path)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.embeddings using (is-emb; _↪_)
open import foundation.equivalences using (is-equiv; _≃_; map-inv-is-equiv)
open import foundation.fibers-of-maps using (equiv-fib-pr1)
open import foundation.fundamental-theorem-of-identity-types using
  ( fundamental-theorem-id)
open import foundation.identity-types using (Id; refl; ap)
open import foundation.propositional-maps using
  ( is-emb-is-prop-map; is-prop-map-is-emb)
open import foundation.propositions using
  ( is-prop; UU-Prop; is-proof-irrelevant-is-prop; is-prop-equiv;
    is-prop-equiv'; type-Prop; is-prop-type-Prop)
open import foundation.sets using (is-set; UU-Set; type-Set; is-set-type-Set)
open import foundation.truncated-types using (is-trunc; is-trunc-is-emb)
open import foundation.truncation-levels using
  ( 𝕋; neg-two-𝕋; neg-one-𝕋; zero-𝕋; succ-𝕋)
open import foundation.type-arithmetic-cartesian-product-types using
  ( equiv-right-swap-Σ)
open import foundation.type-arithmetic-dependent-pair-types using
  ( left-unit-law-Σ-is-contr)
open import foundation.universe-levels using (Level; UU; _⊔_; lsuc)
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2)
  where

  is-subtype : UU (l1 ⊔ l2)
  is-subtype = (x : A) → is-prop (B x)

  is-property : UU (l1 ⊔ l2)
  is-property = is-subtype

subtype : {l1 : Level} (l : Level) (A : UU l1) → UU (l1 ⊔ lsuc l)
subtype l A = A → UU-Prop l

module _
  {l1 l2 : Level} {A : UU l1}
  where

  total-subtype : subtype l2 A → UU (l1 ⊔ l2)
  total-subtype P = Σ A (λ x → pr1 (P x))
```

## Equality in subtypes

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

{- The following is a general construction that will help us show that
   the identity type of a subtype agrees with the identity type of the 
   original type. We already know that the first projection of a family of
   propositions is an embedding, but the following lemma still has its uses. -}

  abstract
    is-contr-total-Eq-substructure :
      {l3 : Level} {P : A → UU l3} →
      is-contr (Σ A B) → (is-subtype P) → (a : A) (b : B a) (p : P a) →
      is-contr (Σ (Σ A P) (λ t → B (pr1 t)))
    is-contr-total-Eq-substructure {l3} {P}
      is-contr-AB is-subtype-P a b p =
      is-contr-equiv
        ( Σ (Σ A B) (λ t → P (pr1 t)))
        ( equiv-right-swap-Σ)
        ( is-contr-equiv
          ( P a)
          ( left-unit-law-Σ-is-contr
            ( is-contr-AB)
            ( pair a b))
          ( is-proof-irrelevant-is-prop (is-subtype-P a) p))

module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (H : is-subtype B)
  where

  Eq-total-subtype : (Σ A B) → (Σ A B) → UU l1
  Eq-total-subtype p p' = Id (pr1 p) (pr1 p') 

  refl-Eq-total-subtype : (p : Σ A B) → Eq-total-subtype p p
  refl-Eq-total-subtype (pair x y) = refl

  Eq-eq-total-subtype : (p p' : Σ A B) → Id p p' → Eq-total-subtype p p'
  Eq-eq-total-subtype p .p refl = refl-Eq-total-subtype p

  abstract
    is-contr-total-Eq-total-subtype :
      (p : Σ A B) → is-contr (Σ (Σ A B) (Eq-total-subtype p))
    is-contr-total-Eq-total-subtype (pair x y) =
      is-contr-total-Eq-substructure (is-contr-total-path x) H x refl y

  abstract
    is-equiv-Eq-eq-total-subtype :
      (p p' : Σ A B) → is-equiv (Eq-eq-total-subtype p p')
    is-equiv-Eq-eq-total-subtype p =
      fundamental-theorem-id p
        ( refl-Eq-total-subtype p)
        ( is-contr-total-Eq-total-subtype p)
        ( Eq-eq-total-subtype p)

  equiv-Eq-eq-total-subtype :
    (p p' : Σ A B) → (Id p p') ≃ (Eq-total-subtype p p')
  pr1 (equiv-Eq-eq-total-subtype p p') = Eq-eq-total-subtype p p'
  pr2 (equiv-Eq-eq-total-subtype p p') = is-equiv-Eq-eq-total-subtype p p'

  eq-subtype :
    {p p' : Σ A B} → Eq-total-subtype p p' → Id p p'
  eq-subtype {p} {p'} =
    map-inv-is-equiv (is-equiv-Eq-eq-total-subtype p p')
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  abstract
    is-emb-pr1 : is-subtype B → is-emb (pr1 {B = B})
    is-emb-pr1 H =
      is-emb-is-prop-map (λ x → is-prop-equiv (equiv-fib-pr1 B x) (H x))

  emb-pr1 : is-subtype B → Σ A B ↪ A
  pr1 (emb-pr1 H) = pr1
  pr2 (emb-pr1 H) = is-emb-pr1 H

  equiv-ap-pr1 : is-subtype B → {s t : Σ A B} → Id s t ≃ Id (pr1 s) (pr1 t)
  pr1 (equiv-ap-pr1 is-subtype-B {s} {t}) = ap pr1
  pr2 (equiv-ap-pr1 is-subtype-B {s} {t}) = is-emb-pr1 is-subtype-B s t

  abstract
    is-subtype-is-emb-pr1 : is-emb (pr1 {B = B}) → is-subtype B
    is-subtype-is-emb-pr1 H x =
      is-prop-equiv' (equiv-fib-pr1 B x) (is-prop-map-is-emb H x)
```

```agda
module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1}
  where
  
  abstract
    is-trunc-is-subtype :
      {P : A → UU l2} → is-subtype P → is-trunc (succ-𝕋 k) A →
      is-trunc (succ-𝕋 k) (Σ A P)
    is-trunc-is-subtype H is-trunc-A =
      is-trunc-is-emb k pr1 (is-emb-pr1 H) is-trunc-A
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {P : A → UU l2}
  where
  
  abstract
    is-prop-is-subtype : is-subtype P → is-prop A → is-prop (Σ A P)
    is-prop-is-subtype = is-trunc-is-subtype neg-two-𝕋

  abstract
    is-set-is-subtype : is-subtype P → is-set A → is-set (Σ A P)
    is-set-is-subtype = is-trunc-is-subtype neg-one-𝕋

  abstract
    is-1-type-is-subtype : is-subtype P → is-1-type A → is-1-type (Σ A P)
    is-1-type-is-subtype = is-trunc-is-subtype zero-𝕋

subprop-Prop :
  {l1 l2 : Level} (A : UU-Prop l1) (P : (x : type-Prop A) → UU-Prop l2) →
  UU-Prop (l1 ⊔ l2)
pr1 (subprop-Prop A P) = Σ (type-Prop A) (λ x → type-Prop (P x))
pr2 (subprop-Prop A P) =
  is-prop-is-subtype (λ x → is-prop-type-Prop (P x)) (is-prop-type-Prop A)

subset-Set :
  {l1 l2 : Level} (A : UU-Set l1) (P : (x : type-Set A) → UU-Prop l2) →
  UU-Set (l1 ⊔ l2)
pr1 (subset-Set A P) = Σ (type-Set A) (λ x → type-Prop (P x))
pr2 (subset-Set A P) =
  is-set-is-subtype (λ x → is-prop-type-Prop (P x)) (is-set-type-Set A)
```
