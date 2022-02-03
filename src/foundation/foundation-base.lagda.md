# Foundation Base

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.foundation-base where

open import foundation.cartesian-product-types using (_×_)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.functions using (_∘_; id)
open import foundation.identity-types using (Id; refl; inv; ap; _∙_)
open import foundation.truncation-levels using
  ( 𝕋; neg-two-𝕋; neg-one-𝕋; zero-𝕋; succ-𝕋)
open import foundation.universe-levels using (Level; UU; _⊔_)
```

## Idea

In this file we set up some preliminary definitions that help us avoid circularity in the dependency graph of this library. All of the defitions will be reintroduced later in their proper files. Files outside of the foundations folder should not be importing `foundation-base`.

## Definitions

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where
  
  _[~]_ : (f g : (x : A) → B x) → UU (l1 ⊔ l2)
  f [~] g = (x : A) → Id (f x) (g x)

  [refl-htpy] : {f : (x : A) → B x} → f [~] f
  [refl-htpy] f = refl

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  [sec] : (A → B) → UU (l1 ⊔ l2)
  [sec] f = Σ (B → A) (λ g → (f ∘ g) [~] id)

  [retr] : (A → B) → UU (l1 ⊔ l2)
  [retr] f = Σ (B → A) (λ g → (g ∘ f) [~] id)

  [is-equiv] : (A → B) → UU (l1 ⊔ l2)
  [is-equiv] f = [sec] f × [retr] f

_[≃]_ : {l1 l2 : Level} → UU l1 → UU l2 → UU (l1 ⊔ l2)
A [≃] B = Σ (A → B) [is-equiv]

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where
  
  [map-inv-is-equiv] : [is-equiv] f → B → A
  [map-inv-is-equiv] H = pr1 (pr1 H)

  [issec-map-inv-is-equiv] :
    (H : [is-equiv] f) → (f ∘ [map-inv-is-equiv] H) [~] id
  [issec-map-inv-is-equiv] H = pr2 (pr1 H)

  [isretr-map-inv-is-equiv] :
    (H : [is-equiv] f) → ([map-inv-is-equiv] H ∘ f) [~] id
  [isretr-map-inv-is-equiv] (pair (pair g G) (pair h H)) x =
    inv (H (g (f x))) ∙ (ap h (G (f x)) ∙ H x)

  [is-equiv-map-inv-is-equiv] :
    (H : [is-equiv] f) → [is-equiv] ([map-inv-is-equiv] H)
  pr1 (pr1 ([is-equiv-map-inv-is-equiv] H)) = f
  pr2 (pr1 ([is-equiv-map-inv-is-equiv] H)) = [isretr-map-inv-is-equiv] H
  pr1 (pr2 ([is-equiv-map-inv-is-equiv] H)) = f
  pr2 (pr2 ([is-equiv-map-inv-is-equiv] H)) = [issec-map-inv-is-equiv] H

module _
  {l : Level}
  where

  [is-contr] : UU l → UU l
  [is-contr] A = Σ A (λ x → (y : A) → Id x y)

  [is-trunc] : 𝕋 → UU l → UU l
  [is-trunc] neg-two-𝕋 A = [is-contr] A
  [is-trunc] (succ-𝕋 k) A = (x y : A) → [is-trunc] k (Id x y)

  [is-prop] : UU l → UU l
  [is-prop] = [is-trunc] neg-one-𝕋

  [is-set] : UU l → UU l
  [is-set] = [is-trunc] zero-𝕋
```
