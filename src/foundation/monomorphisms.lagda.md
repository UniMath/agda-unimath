---
title: Monomorphisms
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.monomorphisms where

open import foundation.dependent-pair-types using (pr1; pr2)
open import foundation.embeddings using (is-emb-Prop; is-emb)
open import foundation.equivalences using (_≃_; map-inv-equiv)
open import foundation.functions using (postcomp; _∘_)
open import foundation.functoriality-function-types using
  ( is-trunc-map-postcomp-is-trunc-map;
    is-trunc-map-is-trunc-map-postcomp)
open import foundation.identity-types using (_＝_; ap)
open import foundation.propositional-maps using
  ( is-emb-is-prop-map; is-prop-map-is-emb)
open import foundation.propositions using
  ( Prop; Π-Prop; is-prop; type-Prop; is-prop-type-Prop)
open import foundation.truncation-levels using (neg-one-𝕋)
open import foundation.universe-levels using (UU; Level; _⊔_; lsuc)
```

## Idea

A function `f : A → B` is a monomorphism if whenever we have two functions `g h : X → A` such that `f ∘ g = f ∘ h`, then in fact `g = h`. The way to state this in Homotopy Type Theory is to say that postcomposition by `f` is an embedding.

## Definition

```agda
module _ {l1 l2 : Level} (l3 : Level)
  {A : UU l1} {B : UU l2} (f : A → B) where

  is-mono-Prop : Prop (l1 ⊔ l2 ⊔ lsuc l3)
  is-mono-Prop = Π-Prop (UU l3) λ X → is-emb-Prop (postcomp X f)

  is-mono : UU (l1 ⊔ l2 ⊔ lsuc l3)
  is-mono = type-Prop is-mono-Prop

  is-prop-is-mono : is-prop is-mono
  is-prop-is-mono = is-prop-type-Prop is-mono-Prop
```

## Properties

If `f : A → B` is a monomorphism then for any `g h : X → A` we have an equivalence `(f ∘ g = f ∘ h) ≃ (g = h)`. In particular, if `f ∘ g = f ∘ h` then `g = h`.

```agda
module _ {l1 l2 : Level} (l3 : Level)
  {A : UU l1} {B : UU l2} (f : A → B)
  (p : is-mono l3 f) {X : UU l3} (g h : X → A) where

  equiv-postcomp-is-mono : (g ＝ h) ≃ ((f ∘ g) ＝ (f ∘ h))
  pr1 equiv-postcomp-is-mono = ap (f ∘_)
  pr2 equiv-postcomp-is-mono = p X g h

  is-injective-postcomp-is-mono : (f ∘ g) ＝ (f ∘ h) → g ＝ h
  is-injective-postcomp-is-mono = map-inv-equiv equiv-postcomp-is-mono
```

A function is a monomorphism if and only if it is an embedding.

```agda
module _ {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) where

  is-mono-is-emb : is-emb f → {l3 : Level} → is-mono l3 f
  is-mono-is-emb f-is-emb X =
    is-emb-is-prop-map
      ( is-trunc-map-postcomp-is-trunc-map neg-one-𝕋 X f
         ( is-prop-map-is-emb f-is-emb))

  is-emb-is-mono : ({l3 : Level} → is-mono l3 f) → is-emb f
  is-emb-is-mono f-is-mono =
    is-emb-is-prop-map
      ( is-trunc-map-is-trunc-map-postcomp neg-one-𝕋 f
         ( λ X → is-prop-map-is-emb (f-is-mono X)))
```
