---
title: Automorphism groups
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module group-theory.automorphism-groups where

open import foundation.connected-components using
  (connected-component; is-path-connected-connected-component; is-trunc-connected-component)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.identity-types using (refl)
open import foundation.propositional-truncations using (unit-trunc-Prop)
open import foundation.truncated-types using (is-trunc)
open import foundation.truncation-levels using (one-𝕋)
open import foundation.universe-levels using (UU; Level; _⊔_; lsuc)

open import group-theory.concrete-groups using (Concrete-Group)
open import group-theory.higher-groups using (∞-Group)
```

## Idea

The automorphim group of `a : A` is the group of symmetries of `a` in `A`.

## Definitions

```agda
module _
  {l : Level} (A : UU l) (a : A)
  where
  
  ∞-Automorphism-Group : ∞-Group l
  pr1 (pr1 ∞-Automorphism-Group) = connected-component A a
  pr2 (pr1 ∞-Automorphism-Group) = pair a (unit-trunc-Prop refl)
  pr2 ∞-Automorphism-Group = is-path-connected-connected-component A a

  Automorphism-Group : is-trunc one-𝕋 A → Concrete-Group l
  pr1 (Automorphism-Group H) = ∞-Automorphism-Group
  pr2 (Automorphism-Group H) = 
    is-trunc-connected-component A a H
      ( pair a (unit-trunc-Prop refl))
      ( pair a (unit-trunc-Prop refl))
```
