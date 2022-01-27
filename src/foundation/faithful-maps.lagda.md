---
title: Univalent Mathematics in Agda
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundation.faithful-maps where

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.embeddings using
  ( is-emb; _↪_; is-emb-is-equiv; map-emb; is-emb-map-emb; id-emb)
open import foundation.equivalences using
  ( is-equiv; _≃_; map-equiv; is-equiv-map-equiv)
open import foundation.functions using (id)
open import foundation.identity-types using (Id; ap)
open import foundation.universe-levels using (Level; UU; _⊔_)
open import foundation.propositional-maps using
  ( is-prop-map-is-emb; is-emb-is-prop-map)
open import foundation.sets using (is-set; UU-Set; type-Set; is-set-type-Set)
open import foundation.truncated-maps using
  ( is-0-map; is-trunc-map-is-trunc-map-ap; is-trunc-map-ap-is-trunc-map;
    is-0-map-pr1)
open import foundation.truncation-levels using (neg-one-𝕋)
```

# Faithful maps

We introduce faithful maps. In analogy to faithful functors, faithful maps are maps that induce embeddings on identity types.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-faithful : (A → B) → UU (l1 ⊔ l2)
  is-faithful f = (x y : A) → is-emb (ap f {x} {y})

faithful-map : {l1 l2 : Level} → UU l1 → UU l2 → UU (l1 ⊔ l2)
faithful-map A B = Σ (A → B) is-faithful

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  map-faithful-map : faithful-map A B → A → B
  map-faithful-map = pr1

  is-faithful-map-faithful-map :
    (f : faithful-map A B) → is-faithful (map-faithful-map f)
  is-faithful-map-faithful-map = pr2

  emb-ap-faithful-map :
    (f : faithful-map A B) {x y : A} →
    Id x y ↪ Id (map-faithful-map f x) (map-faithful-map f y)
  pr1 (emb-ap-faithful-map f {x} {y}) = ap (map-faithful-map f)
  pr2 (emb-ap-faithful-map f {x} {y}) = is-faithful-map-faithful-map f x y

  is-faithful-is-emb : {f : A → B} → is-emb f → is-faithful f
  is-faithful-is-emb {f} H x y = is-emb-is-equiv (H x y)

  faithful-map-emb : (A ↪ B) → faithful-map A B
  pr1 (faithful-map-emb f) = map-emb f
  pr2 (faithful-map-emb f) = is-faithful-is-emb (is-emb-map-emb f)

  is-faithful-is-equiv : {f : A → B} → is-equiv f → is-faithful f
  is-faithful-is-equiv H = is-faithful-is-emb (is-emb-is-equiv H)

  faithful-map-equiv : (A ≃ B) → faithful-map A B
  pr1 (faithful-map-equiv e) = map-equiv e
  pr2 (faithful-map-equiv e) = is-faithful-is-equiv (is-equiv-map-equiv e)

  emb-ap : (f : A ↪ B) (x y : A) → Id x y ↪ Id (map-emb f x) (map-emb f y)
  pr1 (emb-ap f x y) = ap (map-emb f) {x} {y}
  pr2 (emb-ap f x y) = is-faithful-is-emb (is-emb-map-emb f) x y

module _
  {l : Level} {A : UU l}
  where
  
  id-faithful-map : faithful-map A A
  id-faithful-map = faithful-map-emb id-emb

  is-faithful-id-faithful-map : is-faithful (id {A = A})
  is-faithful-id-faithful-map = is-faithful-map-faithful-map id-faithful-map
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  is-0-map-is-faithful : is-faithful f → is-0-map f
  is-0-map-is-faithful H =
    is-trunc-map-is-trunc-map-ap neg-one-𝕋 f
      ( λ x y → is-prop-map-is-emb (H x y))

  is-faithful-is-0-map : is-0-map f → is-faithful f
  is-faithful-is-0-map H x y =
    is-emb-is-prop-map (is-trunc-map-ap-is-trunc-map neg-one-𝕋 f H x y)
```

```agda
module _
  {l1 l2 : Level} {A : UU l1}
  where

  abstract
    is-faithful-pr1 :
      {B : A → UU l2} → ((x : A) → is-set (B x)) → is-faithful (pr1 {B = B})
    is-faithful-pr1 H = is-faithful-is-0-map (is-0-map-pr1 H)

  pr1-faithful-map :
    (B : A → UU-Set l2) → faithful-map (Σ A (λ x → type-Set (B x))) A
  pr1 (pr1-faithful-map B) = pr1
  pr2 (pr1-faithful-map B) = is-faithful-pr1 (λ x → is-set-type-Set (B x))
```
