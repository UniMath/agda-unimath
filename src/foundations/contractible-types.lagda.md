---
title: Univalent Mathematics in Agda
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundations.contractible-types where

open import foundations.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundations.functions using (const; id)
open import foundations.homotopies using (_~_)
open import foundations.identity-types using
  ( Id; refl; inv; _∙_; left-inv)
open import foundations.levels using (Level; UU)
open import foundations.unit-type using (unit; star)
```

# Contractible types

```agda
is-contr :
  {l : Level} → UU l → UU l
is-contr A = Σ A (λ a → (x : A) → Id a x)

abstract
  center :
    {l : Level} {A : UU l} → is-contr A → A
  center (pair c is-contr-A) = c
  
-- We make sure that the contraction is coherent in a straightforward way
eq-is-contr' :
  {l : Level} {A : UU l} → is-contr A → (x y : A) → Id x y
eq-is-contr' (pair c C) x y = (inv (C x)) ∙ (C y)

eq-is-contr :
  {l : Level} {A : UU l} → is-contr A → {x y : A} → Id x y
eq-is-contr C {x} {y} = eq-is-contr' C x y

abstract
  contraction :
    {l : Level} {A : UU l} (is-contr-A : is-contr A) →
    (const A A (center is-contr-A) ~ id)
  contraction C x = eq-is-contr C
  
  coh-contraction :
    {l : Level} {A : UU l} (is-contr-A : is-contr A) →
    Id (contraction is-contr-A (center is-contr-A)) refl
  coh-contraction (pair c C) = left-inv (C c)
```

## Examples of contractible types

```agda
abstract
  is-contr-unit : is-contr unit
  pr1 is-contr-unit = star
  pr2 is-contr-unit star = refl

module _
  {l : Level} {A : UU l}
  where

  abstract
    is-contr-total-path : (a : A) → is-contr (Σ A (λ x → Id a x))
    pr1 (pr1 (is-contr-total-path a)) = a
    pr2 (pr1 (is-contr-total-path a)) = refl
    pr2 (is-contr-total-path a) (pair .a refl) = refl

  abstract
    is-contr-total-path' : (a : A) → is-contr (Σ A (λ x → Id x a))
    pr1 (pr1 (is-contr-total-path' a)) = a
    pr2 (pr1 (is-contr-total-path' a)) = refl
    pr2 (is-contr-total-path' a) (pair .a refl) = refl
```
