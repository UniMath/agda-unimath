---
title: Subtypes
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.subtypes where

open import foundation-core.subtypes public

open import foundation.equality-dependent-function-types using
  ( is-contr-total-Eq-Π)

open import foundation-core.contractible-types using (is-contr)
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
open import foundation-core.logical-equivalences using (_⇔_; iff-Prop)
open import foundation-core.propositions using
  ( UU-Prop; type-Prop; is-equiv-is-prop; is-prop-equiv; is-prop-Π;
    Π-Prop)
open import foundation-core.sets using (is-set; UU-Set)
open import foundation-core.truncation-levels using (𝕋; zero-𝕋)
open import foundation-core.universe-levels using (Level; UU; lsuc; _⊔_)

open import foundation.equality-dependent-function-types
open import foundation.injective-maps using (is-injective; is-injective-is-emb)
open import foundation.logical-equivalences using (is-prop-iff-Prop)
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

  has-same-elements-subtype-Prop :
    {l3 : Level} → subtype l3 A → UU-Prop (l1 ⊔ l2 ⊔ l3)
  has-same-elements-subtype-Prop Q =
    Π-Prop A (λ x → iff-Prop (P x) (Q x))

  has-same-elements-subtype : {l3 : Level} → subtype l3 A → UU (l1 ⊔ l2 ⊔ l3)
  has-same-elements-subtype Q = type-Prop (has-same-elements-subtype-Prop Q)

  refl-has-same-elements-subtype : has-same-elements-subtype P
  pr1 (refl-has-same-elements-subtype x) = id
  pr2 (refl-has-same-elements-subtype x) = id

  is-contr-total-has-same-elements-subtype :
    is-contr (Σ (subtype l2 A) has-same-elements-subtype)
  is-contr-total-has-same-elements-subtype =
    is-contr-total-Eq-Π
      ( λ x Q → P x ⇔ Q)
      ( λ x → is-contr-total-iff (P x))

  extensionality-subtype :
    (Q : subtype l2 A) → (P ＝ Q) ≃ has-same-elements-subtype Q
  extensionality-subtype =
    extensionality-Π P
      ( λ x Q → P x ⇔ Q)
      ( λ x Q → propositional-extensionality (P x) Q)

  has-same-elements-eq-subtype :
    (Q : subtype l2 A) → (P ＝ Q) → has-same-elements-subtype Q
  has-same-elements-eq-subtype Q = map-equiv (extensionality-subtype Q)

  eq-has-same-elements-subtype :
    (Q : subtype l2 A) → has-same-elements-subtype Q → P ＝ Q
  eq-has-same-elements-subtype Q = map-inv-equiv (extensionality-subtype Q)

  refl-extensionality-subtype :
    map-equiv (extensionality-subtype P) refl ＝ (λ x → pair id id)
  refl-extensionality-subtype = refl
```

### The type of all subtypes of a type is a set

```agda
is-set-subtype :
  {l1 l2 : Level} {A : UU l1} → is-set (subtype l2 A)
is-set-subtype {l1} {l2} {A} P Q =
  is-prop-equiv
    ( extensionality-subtype P Q)
    ( is-prop-Π (λ x → is-prop-iff-Prop (P x) (Q x)))

subtype-Set : {l1 : Level} (l2 : Level) → UU l1 → UU-Set (l1 ⊔ lsuc l2)
pr1 (subtype-Set {l1} l2 A) = subtype l2 A
pr2 (subtype-Set {l1} l2 A) = is-set-subtype
```
