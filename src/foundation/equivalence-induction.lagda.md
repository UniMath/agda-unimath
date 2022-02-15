# Equivalence induction

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.equivalence-induction where

open import foundation-core.equivalence-induction public

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using (_≃_; id-equiv)
open import foundation.sections using (sec)
open import foundation.univalence using (is-contr-total-equiv)
open import foundation.universe-levels using (Level; UU)
```

## Idea

Equivalence induction is a condition equivalent to the univalence axiom

## Properties

```agda
abstract
  Ind-equiv : {i j : Level} (A : UU i) (P : (B : UU i) (e : A ≃ B) → UU j) →
    sec (ev-id P)
  Ind-equiv A P =
    IND-EQUIV-is-contr-total-equiv
    ( is-contr-total-equiv A)
    ( λ t → P (pr1 t) (pr2 t))

ind-equiv : {i j : Level} (A : UU i) (P : (B : UU i) (e : A ≃ B) → UU j) →
  P A id-equiv → {B : UU i} (e : A ≃ B) → P B e
ind-equiv A P p {B} = pr1 (Ind-equiv A P) p B
```
