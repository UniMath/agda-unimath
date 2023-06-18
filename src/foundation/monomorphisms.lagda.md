# Monomorphisms

```agda
module foundation.monomorphisms where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.functoriality-function-types
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.propositional-maps
open import foundation-core.propositions
open import foundation-core.truncation-levels
```

</details>

## Idea

A function `f : A → B` is a monomorphism if whenever we have two functions
`g h : X → A` such that `f ∘ g = f ∘ h`, then in fact `g = h`. The way to state
this in Homotopy Type Theory is to say that postcomposition by `f` is an
embedding.

## Definition

```agda
module _
  {l1 l2 : Level} (l3 : Level)
  {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-mono-Prop : Prop (l1 ⊔ l2 ⊔ lsuc l3)
  is-mono-Prop = Π-Prop (UU l3) λ X → is-emb-Prop (postcomp X f)

  is-mono : UU (l1 ⊔ l2 ⊔ lsuc l3)
  is-mono = type-Prop is-mono-Prop

  is-prop-is-mono : is-prop is-mono
  is-prop-is-mono = is-prop-type-Prop is-mono-Prop
```

## Properties

If `f : A → B` is a monomorphism then for any `g h : X → A` we have an
equivalence `(f ∘ g = f ∘ h) ≃ (g = h)`. In particular, if `f ∘ g = f ∘ h` then
`g = h`.

```agda
module _
  {l1 l2 : Level} (l3 : Level)
  {A : UU l1} {B : UU l2} (f : A → B)
  (p : is-mono l3 f) {X : UU l3} (g h : X → A)
  where

  equiv-postcomp-is-mono : (g ＝ h) ≃ ((f ∘ g) ＝ (f ∘ h))
  pr1 equiv-postcomp-is-mono = ap (f ∘_)
  pr2 equiv-postcomp-is-mono = p X g h

  is-injective-postcomp-is-mono : (f ∘ g) ＝ (f ∘ h) → g ＝ h
  is-injective-postcomp-is-mono = map-inv-equiv equiv-postcomp-is-mono
```

A function is a monomorphism if and only if it is an embedding.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

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
