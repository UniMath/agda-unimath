# Induction principles on W-types

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.induction-W-types where

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.elementhood-relation-W-types using (_∈-𝕎_)
open import foundation.equivalences using (_≃_; id-equiv; is-equiv)
open import foundation.function-extensionality using (eq-htpy)
open import foundation.identity-types using (Id; ap; refl)
open import foundation.fibers-of-maps using (fib)
open import foundation.universe-levels using (Level; UU; _⊔_)
open import foundation.W-types using (𝕎; component-𝕎; tree-𝕎)
```

## Idea

There are several induction principles on W-types, besided the induction principle that each W-type comes equipped with by definition. The first is an induction principle formulated with respect to the elementhood relation on W-types. The second is a strong induction principle, analogous to the strong induction principle for the natural numbers.

## Properties

### Induction principle with respect to the elementhood relation

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  where

  □-∈-𝕎 : (𝕎 A B → UU l3) → (𝕎 A B → UU (l1 ⊔ l2 ⊔ l3))
  □-∈-𝕎 P x = (y : 𝕎 A B) → (y ∈-𝕎 x) → P y

  η-□-∈-𝕎 :
    (P : 𝕎 A B → UU l3) → ((x : 𝕎 A B) → P x) → ((x : 𝕎 A B) → □-∈-𝕎 P x)
  η-□-∈-𝕎 P f x y e = f y

  ε-□-∈-𝕎 :
    (P : 𝕎 A B → UU l3) (h : (y : 𝕎 A B) → □-∈-𝕎 P y → P y) →
    ((x : 𝕎 A B) → □-∈-𝕎 P x) → (x : 𝕎 A B) → P x
  ε-□-∈-𝕎 P h f x = h x (f x)

  ind-□-∈-𝕎 :
    (P : 𝕎 A B → UU l3) (h : (y : 𝕎 A B) → □-∈-𝕎 P y → P y) →
    (x : 𝕎 A B) → □-∈-𝕎 P x
  ind-□-∈-𝕎 P h (tree-𝕎 x α) .(α b) (pair b refl) =
    h (α b) (ind-□-∈-𝕎 P h (α b))

  comp-□-∈-𝕎 :
    (P : 𝕎 A B → UU l3) (h : (y : 𝕎 A B) → □-∈-𝕎 P y → P y) →
    (x y : 𝕎 A B) (e : y ∈-𝕎 x) →
    Id (ind-□-∈-𝕎 P h x y e) (h y (ind-□-∈-𝕎 P h y))
  comp-□-∈-𝕎 P h (tree-𝕎 x α) .(α b) (pair b refl) = refl
  
  ind-∈-𝕎 :
    (P : 𝕎 A B → UU l3) (h : (y : 𝕎 A B) → □-∈-𝕎 P y → P y) →
    (x : 𝕎 A B) → P x
  ind-∈-𝕎 P h = ε-□-∈-𝕎 P h (ind-□-∈-𝕎 P h)

  comp-∈-𝕎 :
    (P : 𝕎 A B → UU l3) (h : (y : 𝕎 A B) → □-∈-𝕎 P y → P y) →
    (x : 𝕎 A B) → Id (ind-∈-𝕎 P h x) (h x (λ y e → ind-∈-𝕎 P h y))
  comp-∈-𝕎 P h x =
    ap (h x) (eq-htpy (λ y → eq-htpy (λ e → comp-□-∈-𝕎 P h x y e)))
```

