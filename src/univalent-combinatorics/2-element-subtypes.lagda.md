---
title: 2-element subtypes
---

```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module univalent-combinatorics.2-element-subtypes where

open import foundation.automorphisms using (Aut)
open import foundation.contractible-types using
  ( equiv-is-contr; is-contr-total-path)
open import foundation.coproduct-types using (coprod; inl; inr; is-prop-coprod)
open import foundation.decidable-types using (is-decidable)
open import foundation.decidable-propositions using
  ( decidable-Prop; is-decidable-type-decidable-Prop;
    is-prop-type-decidable-Prop; type-decidable-Prop)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using (_≃_; _∘e_; inv-equiv)
open import foundation.functoriality-coproduct-types using (equiv-coprod)
open import foundation.identity-types using (Id; _∙_; inv)
open import foundation.negation using (¬)
open import foundation.propositional-truncations using
  ( unit-trunc-Prop; type-trunc-Prop)
open import foundation.propositions using
  ( type-Prop; is-prop; is-prop-type-Prop)
open import foundation.sets using (UU-Set; type-Set; is-set-type-Set)
open import foundation.subtypes using (subtype; type-subtype)
open import foundation.type-arithmetic-coproduct-types using
  ( left-distributive-Σ-coprod)
open import foundation.unit-type using (star; is-contr-unit)
open import foundation.universe-levels using (Level; UU; lzero; lsuc; _⊔_)

open import univalent-combinatorics.2-element-types using
  ( has-two-elements; 2-Element-Type; swap-2-Element-Type;
    map-swap-2-Element-Type; compute-swap-2-Element-Type;
    is-inhabited-2-Element-Type)
open import univalent-combinatorics.standard-finite-types using
  ( Fin; is-contr-Fin-one-ℕ)
```

## Idea

A 2-element subtype of a type `A` is a subtype `P` of `A` of which its underlying type `Σ A P` has cardinality 2. Such a subtype is said to be decidable if the proposition `P x` is decidable for every `x : A`.

## Definitions

### The type of 2-element subtypes of a type

```agda
2-Element-Subtype : {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
2-Element-Subtype l2 X =
  Σ (subtype l2 X) (λ P → has-two-elements (type-subtype P))

module _
  {l1 l2 : Level} {X : UU l1} (P : 2-Element-Subtype l2 X)
  where
  
  subtype-2-Element-Subtype : subtype l2 X
  subtype-2-Element-Subtype = pr1 P

  type-prop-2-Element-Subtype : X → UU l2
  type-prop-2-Element-Subtype x = type-Prop (subtype-2-Element-Subtype x)

  is-prop-type-prop-2-Element-Subtype :
    (x : X) → is-prop (type-prop-2-Element-Subtype x)
  is-prop-type-prop-2-Element-Subtype x =
    is-prop-type-Prop (subtype-2-Element-Subtype x)

  type-2-Element-Subtype : UU (l1 ⊔ l2)
  type-2-Element-Subtype = type-subtype subtype-2-Element-Subtype

  has-two-elements-type-2-Element-Subtype :
    has-two-elements type-2-Element-Subtype
  has-two-elements-type-2-Element-Subtype = pr2 P

  2-element-type-2-Element-Subtype : 2-Element-Type (l1 ⊔ l2)
  pr1 2-element-type-2-Element-Subtype = type-2-Element-Subtype
  pr2 2-element-type-2-Element-Subtype = has-two-elements-type-2-Element-Subtype

  is-inhabited-type-2-Element-Subtype : type-trunc-Prop type-2-Element-Subtype
  is-inhabited-type-2-Element-Subtype =
    is-inhabited-2-Element-Type 2-element-type-2-Element-Subtype
```

### The standard 2-element subtype of a pair of distinct elements in a set

```agda
module _
  {l : Level} (X : UU-Set l) {x y : type-Set X} (np : ¬ (Id x y))
  where

  type-prop-standard-2-Element-Subtype : type-Set X → UU l
  type-prop-standard-2-Element-Subtype z = coprod (Id x z) (Id y z)

  is-prop-type-prop-standard-2-Element-Subtype :
    (z : type-Set X) → is-prop (type-prop-standard-2-Element-Subtype z)
  is-prop-type-prop-standard-2-Element-Subtype z =
    is-prop-coprod
      ( λ p q → np (p ∙ inv q))
      ( is-set-type-Set X x z)
      ( is-set-type-Set X y z)

  subtype-standard-2-Element-Subtype : subtype l (type-Set X)
  pr1 (subtype-standard-2-Element-Subtype z) =
    type-prop-standard-2-Element-Subtype z
  pr2 (subtype-standard-2-Element-Subtype z) =
    is-prop-type-prop-standard-2-Element-Subtype z

  type-standard-2-Element-Subtype : UU l
  type-standard-2-Element-Subtype =
    type-subtype subtype-standard-2-Element-Subtype

  equiv-type-standard-2-Element-Subtype :
    Fin 2 ≃ type-standard-2-Element-Subtype
  equiv-type-standard-2-Element-Subtype =
    ( inv-equiv
      ( left-distributive-Σ-coprod (type-Set X) (Id x) (Id y))) ∘e
    ( equiv-coprod
      ( equiv-is-contr
        ( is-contr-Fin-one-ℕ)
        ( is-contr-total-path x))
      ( equiv-is-contr
        ( is-contr-unit)
        ( is-contr-total-path y)))

  has-two-elements-type-standard-2-Element-Subtype :
    has-two-elements type-standard-2-Element-Subtype
  has-two-elements-type-standard-2-Element-Subtype =
    unit-trunc-Prop equiv-type-standard-2-Element-Subtype
```

### Swapping the elements in a 2-element subtype

```agda
module _
  {l1 l2 : Level} {X : UU l1} (P : 2-Element-Subtype l2 X)
  where

  swap-2-Element-Subtype : Aut (type-2-Element-Subtype P)
  swap-2-Element-Subtype =
    swap-2-Element-Type (2-element-type-2-Element-Subtype P)

  map-swap-2-Element-Subtype :
    type-2-Element-Subtype P → type-2-Element-Subtype P
  map-swap-2-Element-Subtype =
    map-swap-2-Element-Type (2-element-type-2-Element-Subtype P)

  compute-swap-2-Element-Subtype :
    (x y : type-2-Element-Subtype P) → ¬ (Id x y) →
    Id (map-swap-2-Element-Subtype x) y
  compute-swap-2-Element-Subtype =
    compute-swap-2-Element-Type (2-element-type-2-Element-Subtype P)
```
