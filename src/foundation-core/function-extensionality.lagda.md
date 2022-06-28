---
title: Function extensionality
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation-core.function-extensionality where

open import foundation-core.dependent-pair-types using (pair; pr1; pr2)
open import foundation-core.equivalences using
  ( is-equiv; _≃_; map-inv-is-equiv; issec-map-inv-is-equiv;
    isretr-map-inv-is-equiv; is-equiv-map-inv-is-equiv)
open import foundation-core.functions using (_∘_; id; precomp)
open import foundation-core.homotopies using (_~_; refl-htpy)
open import foundation-core.identity-types using (_＝_; refl; ap)
open import foundation-core.universe-levels using (Level; UU; _⊔_)
```

## Idea

The function extensionality axiom asserts that identifications of (dependent) functions are equivalently described as pointwise equalities between them. In other words, a function is completely determined by its values.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where
  
  htpy-eq : {f g : (x : A) → B x} → (f ＝ g) → (f ~ g)
  htpy-eq refl = refl-htpy

  FUNEXT : (f : (x : A) → B x) → UU (l1 ⊔ l2)
  FUNEXT f = (g : (x : A) → B x) → is-equiv (htpy-eq {f} {g})
```

## Postulate

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where
  
  postulate funext : (f : (x : A) → B x) → FUNEXT f

  equiv-funext : {f g : (x : A) → B x} → (f ＝ g) ≃ (f ~ g)
  pr1 (equiv-funext {f = f} {g}) = htpy-eq
  pr2 (equiv-funext {f = f} {g}) = funext f g

  abstract
    eq-htpy : {f g : (x : A) → B x} → (f ~ g) → f ＝ g
    eq-htpy = map-inv-is-equiv (funext _ _)
  
    issec-eq-htpy :
      {f g : (x : A) → B x} → (htpy-eq ∘ (eq-htpy {f = f} {g = g})) ~ id
    issec-eq-htpy = issec-map-inv-is-equiv (funext _ _)
  
    isretr-eq-htpy :
      {f g : (x : A) → B x} → (eq-htpy ∘ (htpy-eq {f = f} {g = g})) ~ id
    isretr-eq-htpy = isretr-map-inv-is-equiv (funext _ _)

    is-equiv-eq-htpy :
      (f g : (x : A) → B x) → is-equiv (eq-htpy {f = f} {g = g})
    is-equiv-eq-htpy f g = is-equiv-map-inv-is-equiv (funext _ _)

    eq-htpy-refl-htpy :
      (f : (x : A) → B x) → eq-htpy (refl-htpy {f = f}) ＝ refl
    eq-htpy-refl-htpy f = isretr-eq-htpy refl

  equiv-eq-htpy : {f g : (x : A) → B x} → (f ~ g) ≃ (f ＝ g)
  pr1 (equiv-eq-htpy {f = f} {g}) = eq-htpy
  pr2 (equiv-eq-htpy {f = f} {g}) = is-equiv-eq-htpy f g
```

```agda
square-htpy-eq :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → B) →
  ( g h : B → C) →
  ( (λ (p : (y : B) → g y ＝ h y) (x : A) → p (f x)) ∘ htpy-eq) ~
  ( htpy-eq ∘ (ap (precomp f C)))
square-htpy-eq f g .g refl = refl
```
