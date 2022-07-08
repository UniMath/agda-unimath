---
title: The universal multiset
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.universal-multiset where

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using
  ( _∘e_; inv-equiv; map-inv-equiv; _≃_; isretr-map-inv-equiv)
open import foundation.functoriality-w-types using (equiv-𝕎)
open import foundation.identity-types using (tr; inv)
open import foundation.multisets using (𝕍)
open import foundation.raising-universe-levels using
  ( equiv-raise; map-inv-raise)
open import foundation.small-multisets using
  ( resize-𝕍; is-small-multiset-𝕍; is-small-𝕍)
open import foundation.small-types using
  ( is-small-lsuc; type-is-small; equiv-is-small)
open import foundation.small-universes using (is-small-universe)
open import foundation.universe-levels using (Level; lsuc)
open import foundation.w-types using (tree-𝕎; 𝕎)
```

## Idea

The universal multiset of universe level `l` is the multiset of level `lsuc l` built out of `𝕍 l` and resizings of the multisets it contains

## Definition
```agda
universal-multiset-𝕍 : (l : Level) → 𝕍 (lsuc l)
universal-multiset-𝕍 l =
  tree-𝕎
    ( 𝕍 l)
    ( λ X → resize-𝕍 X (is-small-multiset-𝕍 is-small-lsuc X))
```

## Properties

### If `UU l1` is `UU l`-small, then the universal multiset of level `l1` is `UU l`-small

```agda
is-small-universal-multiset-𝕍 :
  (l : Level) {l1 : Level} →
  is-small-universe l l1 → is-small-𝕍 l (universal-multiset-𝕍 l1)
is-small-universal-multiset-𝕍 l {l1} (pair (pair U e) H) =
  pair
    ( pair
      ( 𝕎 U (λ x → pr1 (H (map-inv-equiv e x))))
      ( equiv-𝕎
        ( λ u → type-is-small (H (map-inv-equiv e u)))
        ( e)
        ( λ X →
          tr ( λ t → X ≃ pr1 (H t))
             ( inv (isretr-map-inv-equiv e X))
             ( pr2 (H X)))))
    ( f)
    where
    f : (X : 𝕍 l1) →
        is-small-𝕍 l
          ( resize-𝕍 X (is-small-multiset-𝕍 is-small-lsuc X))
    f (tree-𝕎 A α) =
      pair
        ( pair
          ( type-is-small (H A))
          ( equiv-is-small (H A) ∘e inv-equiv (equiv-raise (lsuc l1) A)))
        ( λ x → f (α (map-inv-raise x)))
```
