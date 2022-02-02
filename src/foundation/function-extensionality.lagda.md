# Function extensionality

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.function-extensionality where

open import foundation.dependent-pair-types using (pair; pr1; pr2)
open import foundation.equivalences using
  ( _≃_; is-fiberwise-equiv; map-inv-is-equiv; issec-map-inv-is-equiv;
    isretr-map-inv-is-equiv; is-equiv; is-equiv-map-inv-is-equiv)
open import foundation.functions using (_∘_; id)
open import foundation.homotopies using (_~_; refl-htpy)
open import foundation.identity-types using (Id; refl)
open import foundation.universe-levels using (Level; UU; _⊔_)
```

## Idea

The function extensionality axiom asserts that identifications of (dependent) functions are equivalently described as pointwise equalities between them. In other words, a function is completely determined by its values.

## Definition

```agda
htpy-eq :
  {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x} →
  (Id f g) → (f ~ g)
htpy-eq refl = refl-htpy

FUNEXT :
  {i j : Level} {A : UU i} {B : A → UU j} →
  (f : (x : A) → B x) → UU (i ⊔ j)
FUNEXT f = is-fiberwise-equiv (λ g → htpy-eq {f = f} {g = g})
```

## Postulate

```agda
postulate funext : {i j : Level} {A : UU i} {B : A → UU j} (f : (x : A) → B x) → FUNEXT f

equiv-funext : {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x} →
  (Id f g) ≃ (f ~ g)
pr1 (equiv-funext {f = f} {g}) = htpy-eq
pr2 (equiv-funext {f = f} {g}) = funext f g

abstract
  eq-htpy :
    {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x} →
    (f ~ g) → Id f g
  eq-htpy = map-inv-is-equiv (funext _ _)
  
  issec-eq-htpy :
    {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x} →
    ((htpy-eq {f = f} {g = g}) ∘ (eq-htpy {f = f} {g = g})) ~ id
  issec-eq-htpy = issec-map-inv-is-equiv (funext _ _)
  
  isretr-eq-htpy :
    {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x} →
    ((eq-htpy {f = f} {g = g}) ∘ (htpy-eq {f = f} {g = g})) ~ id
  isretr-eq-htpy = isretr-map-inv-is-equiv (funext _ _)

  is-equiv-eq-htpy :
    {i j : Level} {A : UU i} {B : A → UU j}
    (f g : (x : A) → B x) → is-equiv (eq-htpy {f = f} {g = g})
  is-equiv-eq-htpy f g = is-equiv-map-inv-is-equiv (funext _ _)

  eq-htpy-refl-htpy :
    {i j : Level} {A : UU i} {B : A → UU j}
    (f : (x : A) → B x) → Id (eq-htpy (refl-htpy {f = f})) refl
  eq-htpy-refl-htpy f = isretr-eq-htpy refl

equiv-eq-htpy :
  {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x} →
  (f ~ g) ≃ Id f g
pr1 (equiv-eq-htpy {f = f} {g}) = eq-htpy
pr2 (equiv-eq-htpy {f = f} {g}) = is-equiv-eq-htpy f g
```
