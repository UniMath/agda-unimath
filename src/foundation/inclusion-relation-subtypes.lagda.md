---
title: The inclusion relation on subtypes
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.inclusion-relation-subtypes where

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functions
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositional-extensionality
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.preorders
open import order-theory.posets
```

## Definition

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  inclusion-rel-subtype-Prop :
    {l2 l3 : Level} → subtype l2 A → subtype l3 A → UU-Prop (l1 ⊔ l2 ⊔ l3)
  inclusion-rel-subtype-Prop P Q =
    Π-Prop A (λ x → hom-Prop (P x) (Q x))
  
  _⊆_ :
    {l2 l3 : Level} (P : subtype l2 A) (Q : subtype l3 A) → UU (l1 ⊔ l2 ⊔ l3)
  P ⊆ Q = type-Prop (inclusion-rel-subtype-Prop P Q)

  is-prop-inclusion-rel-subtype :
    {l2 l3 : Level} (P : subtype l2 A) (Q : subtype l3 A) → is-prop (P ⊆ Q)
  is-prop-inclusion-rel-subtype P Q =
    is-prop-type-Prop (inclusion-rel-subtype-Prop P Q)
```

## Properties

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  refl-⊆ : {l2 : Level} (P : subtype l2 A) → P ⊆ P
  refl-⊆ P x = id

  trans-⊆ :
    {l2 l3 l4 : Level}
    (P : subtype l2 A) (Q : subtype l3 A) (R : subtype l4 A) →
    P ⊆ Q → Q ⊆ R → P ⊆ R
  trans-⊆ P Q R H K x = K x ∘ H x

  equiv-antisymmetric-⊆ :
    {l2 l3 : Level} (P : subtype l2 A) (Q : subtype l3 A) → P ⊆ Q → Q ⊆ P →
    (x : A) → is-in-subtype P x ≃ is-in-subtype Q x
  equiv-antisymmetric-⊆ P Q H K x =
    equiv-prop
      ( is-prop-is-in-subtype P x)
      ( is-prop-is-in-subtype Q x)
      ( H x)
      ( K x)

  antisymmetric-⊆ :
    {l2 : Level} (P Q : subtype l2 A) → P ⊆ Q → Q ⊆ P → Id P Q
  antisymmetric-⊆ P Q H K = eq-htpy (λ x → eq-iff (H x) (K x))

  powerset-Preorder : (l2 : Level) → Preorder (l1 ⊔ lsuc l2) (l1 ⊔ l2)
  pr1 (powerset-Preorder l2) = subtype l2 A
  pr1 (pr2 (powerset-Preorder l2)) = inclusion-rel-subtype-Prop
  pr1 (pr2 (pr2 (powerset-Preorder l2))) = refl-⊆
  pr2 (pr2 (pr2 (powerset-Preorder l2))) P Q R H K = trans-⊆ P Q R K H

  powerset-Poset : (l2 : Level) → Poset (l1 ⊔ lsuc l2) (l1 ⊔ l2)
  pr1 (powerset-Poset l2) = subtype l2 A
  pr1 (pr2 (powerset-Poset l2)) = inclusion-rel-subtype-Prop
  pr1 (pr1 (pr2 (pr2 (powerset-Poset l2)))) = refl-⊆
  pr2 (pr1 (pr2 (pr2 (powerset-Poset l2)))) P Q R H K = trans-⊆ P Q R K H
  pr2 (pr2 (pr2 (powerset-Poset l2))) = antisymmetric-⊆
```
