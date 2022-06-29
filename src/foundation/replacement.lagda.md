---
title: The replacement axiom for type theory
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.replacement where

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.embeddings using (id-emb)
open import foundation.homotopies using (refl-htpy)
open import foundation.images using (im)
open import foundation.locally-small-types using (is-locally-small)
open import foundation.small-types using (is-small; is-small-equiv')
open import foundation.surjective-maps using (is-surjective)
open import foundation.uniqueness-image using (equiv-equiv-slice-uniqueness-im)
open import foundation.universal-property-image using
  ( is-image-is-surjective)
open import foundation.universe-levels using (Level; UUω; UU)
```

## Idea

The type theoretic replacement axiom asserts that the image of a map `f : A → B` from a small type `A` into a locally small type `B` is small.

## Definition

```agda
Replacement : (l : Level) → UUω
Replacement l =
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-small l A → is-locally-small l B → is-small l (im f)
```

## Properties

### If `f` is a surjective map from a small type into a locally small type, then Replacement implies that the codomain is small.

```agda
is-small-codomain-by-replacement :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  Replacement l3 → is-surjective f → is-small l3 A → is-locally-small l3 B →
  is-small l3 B
is-small-codomain-by-replacement {f = f} R H K L =
  is-small-equiv' _
    ( im f)
    ( equiv-equiv-slice-uniqueness-im f id-emb
      ( pair f refl-htpy)
      ( is-image-is-surjective f id-emb (pair f refl-htpy) H))
    ( R f K L)
```
