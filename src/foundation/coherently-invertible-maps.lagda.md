---
title: Univalent Mathematics in Agda
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundation.coherently-invertible-maps where

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.functions using (_∘_; id)
open import foundation.homotopies using (_~_; _·r_; _·l_)
open import foundation.identity-types using
  ( inv; _∙_; ap; inv-con)
open import foundation.universe-levels using (Level; UU; _⊔_)
```

# Coherently invertible maps

In this file we introduce coherently invertible maps, which are also known as half-adjoint equivalences. We will show that any equivalence is coherently invertible in `equivalences`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where
  
  coherence-is-coherently-invertible :
    (g : B → A) (G : (f ∘ g) ~ id) (H : (g ∘ f) ~ id) → UU (l1 ⊔ l2)
  coherence-is-coherently-invertible g G H = (G ·r f) ~ (f ·l H)

  is-coherently-invertible : UU (l1 ⊔ l2)
  is-coherently-invertible =
    Σ ( B → A)
      ( λ g → Σ ((f ∘ g) ~ id)
        ( λ G → Σ ((g ∘ f) ~ id)
          (λ H → coherence-is-coherently-invertible g G H)))

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  inv-is-coherently-invertible : is-coherently-invertible f → B → A
  inv-is-coherently-invertible = pr1

  issec-inv-is-coherently-invertible :
    (H : is-coherently-invertible f) → (f ∘ inv-is-coherently-invertible H) ~ id
  issec-inv-is-coherently-invertible H = pr1 (pr2 H)
  
  isretr-inv-is-coherently-invertible :
    (H : is-coherently-invertible f) → (inv-is-coherently-invertible H ∘ f) ~ id
  isretr-inv-is-coherently-invertible H = pr1 (pr2 (pr2 H))

  coh-inv-is-coherently-invertible :
    (H : is-coherently-invertible f) →
    coherence-is-coherently-invertible f
      ( inv-is-coherently-invertible H)
      ( issec-inv-is-coherently-invertible H)
      ( isretr-inv-is-coherently-invertible H)
  coh-inv-is-coherently-invertible H = pr2 (pr2 (pr2 H))
```
