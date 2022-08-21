---
title: Subtypes
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.subtypes where

open import foundation-core.subtypes public

open import foundation-core.dependent-pair-types using (Σ; pr1; pr2; pair)
open import foundation-core.embeddings using (_↪_; map-emb)
open import foundation-core.equivalences using
  ( _≃_; map-equiv; is-equiv; map-inv-is-equiv; isretr-map-inv-is-equiv;
    map-inv-equiv)
open import foundation-core.functions using (_∘_; id)
open import foundation-core.functoriality-dependent-pair-types using
  ( equiv-Σ; map-Σ; is-equiv-map-Σ)
open import foundation-core.homotopies using (_~_)
open import foundation-core.identity-types using (tr; _＝_; refl)
open import foundation-core.logical-equivalences using (_⇔_)
open import foundation-core.propositions using
  ( UU-Prop; type-Prop; is-equiv-is-prop)
open import foundation-core.truncation-levels using (𝕋; zero-𝕋)
open import foundation-core.universe-levels using (Level; UU; lsuc; _⊔_)

open import foundation.equality-dependent-function-types
open import foundation.injective-maps using (is-injective; is-injective-is-emb)
open import foundation.propositional-extensionality
```

## Definition

### A second definition of the type of subtypes

```agda
Subtype : {l1 : Level} (l2 l3 : Level) (A : UU l1) → UU (l1 ⊔ lsuc l2 ⊔ lsuc l3)
Subtype l2 l3 A =
  Σ ( A → UU-Prop l2)
    ( λ P →
      Σ ( Σ (UU l3) (λ X → X ↪ A))
        ( λ i →
          Σ ( pr1 i ≃ Σ A (type-Prop ∘ P))
            ( λ e → map-emb (pr2 i) ~ (pr1 ∘ map-equiv e))))
```

## Properties

### The inclusion of a subtype into the ambient type is injective

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : subtype l2 A)
  where
  
  is-injective-inclusion-subtype : is-injective (inclusion-subtype B)
  is-injective-inclusion-subtype =
    is-injective-is-emb (is-emb-inclusion-subtype B)
```

### Equality in the type of all subtypes

```agda
module _
  {l1 l2 : Level} {A : UU l1} (P : subtype l2 A)
  where

  Eq-subtype : subtype l2 A → UU (l1 ⊔ l2)
  Eq-subtype Q = (x : A) → P x ⇔ Q x

  extensionality-subtype : (Q : subtype l2 A) → (P ＝ Q) ≃ Eq-subtype Q
  extensionality-subtype =
    extensionality-Π P
      ( λ x Q → P x ⇔ Q)
      ( λ x Q → propositional-extensionality (P x) Q)

  map-extensionality-subtype : (Q : subtype l2 A) → (P ＝ Q) → Eq-subtype Q
  map-extensionality-subtype Q = map-equiv (extensionality-subtype Q)

  map-inv-extensionality-subtype : (Q : subtype l2 A) → Eq-subtype Q → P ＝ Q
  map-inv-extensionality-subtype Q = map-inv-equiv (extensionality-subtype Q)

  refl-extensionality-subtype :
    map-equiv (extensionality-subtype P) refl ＝ (λ x → pair id id)
  refl-extensionality-subtype = refl
```
