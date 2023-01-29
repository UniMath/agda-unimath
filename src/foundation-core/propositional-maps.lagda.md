---
title: Propositional maps
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation-core.propositional-maps where

open import foundation-core.contractible-types using
  ( is-contr-equiv'; is-contr; is-contr-equiv)
open import foundation-core.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation-core.embeddings using
  ( is-emb; _↪_; map-emb; is-emb-map-emb)
open import foundation-core.equivalences using (is-equiv-comp; _≃_)
open import foundation-core.fibers-of-maps using (fib; equiv-fib; fib')
open import foundation-core.functions using (_∘_)
open import foundation-core.functoriality-dependent-pair-types using
  ( equiv-tot)
open import foundation-core.fundamental-theorem-of-identity-types using
  ( fundamental-theorem-id; fundamental-theorem-id')
open import foundation-core.identity-types using ( refl; ap; inv)
open import foundation-core.propositions using
  ( is-prop; is-proof-irrelevant-is-prop; is-prop-is-proof-irrelevant; Prop)
open import foundation-core.universe-levels using (Level; UU; _⊔_)
```

## Idea

A map is said to be propositional if its fibers are propositions. This condition is equivalent to being an embedding.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-prop-map : (A → B) → UU (l1 ⊔ l2)
  is-prop-map f = (b : B) → is-prop (fib f b)
```

## Properties

### The fibers of a map are propositions if and only if it is an embedding

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  abstract
    is-emb-is-prop-map : is-prop-map f → is-emb f
    is-emb-is-prop-map is-prop-map-f x =
      fundamental-theorem-id
        ( is-contr-equiv'
          ( fib f (f x))
          ( equiv-fib f (f x))
          ( is-proof-irrelevant-is-prop (is-prop-map-f (f x)) (pair x refl)))
        ( λ y → ap f)

  abstract
    is-prop-map-is-emb : is-emb f → is-prop-map f
    is-prop-map-is-emb is-emb-f y =
      is-prop-is-proof-irrelevant α
      where
      α : (t : fib f y) → is-contr (fib f y)
      α (pair x refl) =
        is-contr-equiv
          ( fib' f (f x))
          ( equiv-fib f (f x))
          ( fundamental-theorem-id'
            ( λ y → ap f)
            ( λ y → is-emb-f x y))

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-prop-map-emb : (f : B ↪ A) → is-prop-map (map-emb f)
    is-prop-map-emb f = is-prop-map-is-emb (is-emb-map-emb f)

  fib-emb-Prop : A ↪ B → B → Prop (l1 ⊔ l2)
  pr1 (fib-emb-Prop f y) = fib (map-emb f) y
  pr2 (fib-emb-Prop f y) = is-prop-map-is-emb (is-emb-map-emb f) y
```
