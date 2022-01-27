---
title: Univalent Mathematics in Agda
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundation.empty-type where

open import foundation.cartesian-product-types using (_×_)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.embeddings using (is-emb; _↪_)
open import foundation.equivalences using
  ( is-equiv; is-equiv-has-inverse; _≃_; inv-equiv; _∘e_)
open import foundation.functions using (_∘_; id)
open import foundation.homotopies using (_~_)
open import foundation.levels using (Level; lzero; UU)
open import foundation.propositions using (is-prop; UU-Prop)
open import foundation.raising-universe-levels using (raise; equiv-raise)
open import foundation.truncated-types using (is-trunc; is-trunc-is-prop)
open import foundation.truncation-levels using (𝕋; succ-𝕋)
```

# The empty type

```agda
data empty : UU lzero where

ind-empty : {l : Level} {P : empty → UU l} → ((x : empty) → P x)
ind-empty ()

ex-falso : {l : Level} {A : UU l} → empty → A
ex-falso = ind-empty

is-empty : {l : Level} → UU l → UU l
is-empty A = A → empty

is-nonempty : {l : Level} → UU l → UU l
is-nonempty A = is-empty (is-empty A)
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

## Any map into an empty type is an equivalence

```agda
abstract
  is-equiv-is-empty :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-empty B → is-equiv f
  is-equiv-is-empty f H =
    is-equiv-has-inverse
      ( ex-falso ∘ H)
      ( λ y → ex-falso (H y))
      ( λ x → ex-falso (H (f x)))

abstract
  is-equiv-is-empty' :
    {l : Level} {A : UU l} (f : is-empty A) → is-equiv f
  is-equiv-is-empty' f = is-equiv-is-empty f id

equiv-is-empty :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → is-empty A → is-empty B → A ≃ B
equiv-is-empty f g =
  ( inv-equiv (pair g (is-equiv-is-empty g id))) ∘e
  ( pair f (is-equiv-is-empty f id))
```

```agda
abstract
  is-prop-empty : is-prop empty
  is-prop-empty ()

empty-Prop : UU-Prop lzero
pr1 empty-Prop = empty
pr2 empty-Prop = is-prop-empty
```

```agda
raise-empty : (l : Level) → UU l
raise-empty l = raise l empty

equiv-raise-empty : (l : Level) → empty ≃ raise-empty l
equiv-raise-empty l = equiv-raise l empty
```

```agda
abstract
  is-trunc-empty : (k : 𝕋) → is-trunc (succ-𝕋 k) empty
  is-trunc-empty k ()

abstract
  is-trunc-is-empty :
    {l : Level} (k : 𝕋) {A : UU l} → is-empty A → is-trunc (succ-𝕋 k) A
  is-trunc-is-empty k f = is-trunc-is-prop k (λ x → ex-falso (f x))
```

## Left zero law for cartesian products

```agda
module _
  {l : Level} (X : UU l)
  where

  inv-pr1-prod-empty : empty → empty × X
  inv-pr1-prod-empty ()

  issec-inv-pr1-prod-empty : (pr1 ∘ inv-pr1-prod-empty) ~ id
  issec-inv-pr1-prod-empty ()

  isretr-inv-pr1-prod-empty : (inv-pr1-prod-empty ∘ pr1) ~ id
  isretr-inv-pr1-prod-empty (pair () x)

  is-equiv-pr1-prod-empty : is-equiv (pr1 {A = empty} {B = λ t → X})
  is-equiv-pr1-prod-empty =
    is-equiv-has-inverse
      inv-pr1-prod-empty
      issec-inv-pr1-prod-empty
      isretr-inv-pr1-prod-empty

  left-zero-law-prod : (empty × X) ≃ empty
  pr1 left-zero-law-prod = pr1
  pr2 left-zero-law-prod = is-equiv-pr1-prod-empty
```

## Right zero law for cartesian products

```agda
module _
  {l : Level} (X : UU l)
  where

  inv-pr2-prod-empty : empty → (X × empty)
  inv-pr2-prod-empty ()

  issec-inv-pr2-prod-empty : (pr2 ∘ inv-pr2-prod-empty) ~ id
  issec-inv-pr2-prod-empty ()

  isretr-inv-pr2-prod-empty : (inv-pr2-prod-empty ∘ pr2) ~ id
  isretr-inv-pr2-prod-empty (pair x ())

  is-equiv-pr2-prod-empty : is-equiv (pr2 {A = X} {B = λ x → empty})
  is-equiv-pr2-prod-empty =
    is-equiv-has-inverse
      inv-pr2-prod-empty
      issec-inv-pr2-prod-empty
      isretr-inv-pr2-prod-empty

  right-zero-law-prod : (X × empty) ≃ empty
  pr1 right-zero-law-prod = pr2
  pr2 right-zero-law-prod = is-equiv-pr2-prod-empty
```

## Right absorption law for dependent pair types and for cartesian products

```agda
module _
  {l : Level} (A : UU l)
  where
  
  map-right-absorption-Σ : Σ A (λ x → empty) → empty
  map-right-absorption-Σ (pair x ())
  
  is-equiv-map-right-absorption-Σ : is-equiv map-right-absorption-Σ
  is-equiv-map-right-absorption-Σ = is-equiv-is-empty' map-right-absorption-Σ

  right-absorption-Σ : Σ A (λ x → empty) ≃ empty
  right-absorption-Σ =
    pair map-right-absorption-Σ is-equiv-map-right-absorption-Σ
```

## Left absorption law for dependent pair types

```agda
module _
  {l : Level} (A : empty → UU l)
  where

  map-left-absorption-Σ : Σ empty A → empty
  map-left-absorption-Σ = pr1
  
  is-equiv-map-left-absorption-Σ : is-equiv map-left-absorption-Σ
  is-equiv-map-left-absorption-Σ =
    is-equiv-is-empty' map-left-absorption-Σ
  
  left-absorption-Σ : Σ empty A ≃ empty
  pr1 left-absorption-Σ = map-left-absorption-Σ
  pr2 left-absorption-Σ = is-equiv-map-left-absorption-Σ
```

## Right absorption law for cartesian product types

```agda
module _
  {l : Level} {A : UU l}
  where
  
  map-right-absorption-prod : A × empty → empty
  map-right-absorption-prod = map-right-absorption-Σ A

  is-equiv-map-right-absorption-prod : is-equiv map-right-absorption-prod
  is-equiv-map-right-absorption-prod = is-equiv-map-right-absorption-Σ A

  right-absorption-prod : (A × empty) ≃ empty
  right-absorption-prod = right-absorption-Σ A

is-empty-right-factor-is-empty-prod :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → is-empty (A × B) → A → is-empty B
is-empty-right-factor-is-empty-prod f a b = f (pair a b)
```

## Left absorption law for cartesian products

```agda
module _
  {l : Level} (A : UU l)
  where

  map-left-absorption-prod : empty × A → empty
  map-left-absorption-prod = map-left-absorption-Σ (λ x → A)
  
  is-equiv-map-left-absorption-prod : is-equiv map-left-absorption-prod
  is-equiv-map-left-absorption-prod =
    is-equiv-map-left-absorption-Σ (λ x → A)
    
  left-absorption-prod : (empty × A) ≃ empty
  left-absorption-prod = left-absorption-Σ (λ x → A)

is-empty-left-factor-is-empty-prod :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → is-empty (A × B) → B → is-empty A
is-empty-left-factor-is-empty-prod f b a = f (pair a b)
```
