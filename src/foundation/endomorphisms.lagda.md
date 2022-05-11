---
title: endomorphisms
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.endomorphisms where

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.functions using (id; _∘_)
open import foundation.identity-types using (refl)
open import foundation.sets using
  ( UU-Set; type-Set; is-set; is-set-function-type; is-set-type-Set)
open import foundation.unit-type using (star)
open import foundation.universe-levels using (Level; UU)

open import group-theory.monoids using (Monoid)
open import group-theory.semigroups using (Semigroup)

open import structured-types.pointed-types
open import structured-types.wild-monoids
```

## Idea

An endomorphism on a type `A` is a map `A → A`.

## Definitions

### Endomorphisms

```agda
endo : {l : Level} → UU l → UU l
endo A = A → A

is-set-endo : {l : Level} {A : UU l} → is-set A → is-set (endo A)
is-set-endo H = is-set-function-type H

endo-Set : {l : Level} → UU-Set l → UU-Set l
pr1 (endo-Set A) = endo (type-Set A)
pr2 (endo-Set A) = is-set-endo (is-set-type-Set A)

endo-Pointed-Type : {l : Level} → UU l → Pointed-Type l
pr1 (endo-Pointed-Type X) = X → X
pr2 (endo-Pointed-Type X) = id

endo-Wild-Monoid : {l : Level} → UU l → Wild-Monoid l
pr1 (pr1 (endo-Wild-Monoid X)) = endo-Pointed-Type X
pr1 (pr2 (pr1 (endo-Wild-Monoid X))) g f = g ∘ f
pr1 (pr2 (pr2 (pr1 (endo-Wild-Monoid X)))) f = refl
pr1 (pr2 (pr2 (pr2 (pr1 (endo-Wild-Monoid X))))) f = refl
pr2 (pr2 (pr2 (pr2 (pr1 (endo-Wild-Monoid X))))) = refl
pr1 (pr2 (endo-Wild-Monoid X)) h g f = refl
pr1 (pr2 (pr2 (endo-Wild-Monoid X))) g f = refl
pr1 (pr2 (pr2 (pr2 (endo-Wild-Monoid X)))) g f = refl
pr1 (pr2 (pr2 (pr2 (pr2 (endo-Wild-Monoid X))))) g f = refl
pr2 (pr2 (pr2 (pr2 (pr2 (endo-Wild-Monoid X))))) = star

endo-Semigroup : {l : Level} → UU-Set l → Semigroup l
pr1 (endo-Semigroup X) = endo-Set X
pr1 (pr2 (endo-Semigroup X)) g f = g ∘ f
pr2 (pr2 (endo-Semigroup X)) h g f = refl

endo-Monoid : {l : Level} → UU-Set l → Monoid l
pr1 (endo-Monoid X) = endo-Semigroup X
pr1 (pr2 (endo-Monoid X)) = id
pr1 (pr2 (pr2 (endo-Monoid X))) f = refl
pr2 (pr2 (pr2 (endo-Monoid X))) f = refl
```
