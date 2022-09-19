---
title: Mere equivalences
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.mere-equivalences where

open import foundation.decidable-equality using
  ( has-decidable-equality; has-decidable-equality-Prop;
    has-decidable-equality-equiv; has-decidable-equality-equiv')
open import foundation.equivalences using (_≃_; id-equiv; inv-equiv; _∘e_)
open import foundation.functoriality-propositional-truncation using
  ( map-trunc-Prop)
open import foundation.mere-equality using (mere-eq)
open import foundation.propositional-truncations using
  ( trunc-Prop; unit-trunc-Prop; map-universal-property-trunc-Prop;
    apply-universal-property-trunc-Prop)
open import foundation.propositions using
  ( Prop; type-Prop; is-prop; is-prop-type-Prop)
open import foundation.sets using (is-set)
open import foundation.truncated-types using
  ( is-trunc; is-trunc-Prop; is-trunc-equiv; is-trunc-equiv')
open import foundation.truncation-levels using (𝕋; zero-𝕋)
open import foundation.univalence using (eq-equiv)
open import foundation.universe-levels using (Level; UU; _⊔_)
```

## Idea

Two types `X` and `Y` are said to be merely equivalent, if there exists an equivalence from `X` to `Y`. Propositional truncations are used to express mere equivalence.

## Definition

```agda
mere-equiv-Prop :
  {l1 l2 : Level} → UU l1 → UU l2 → Prop (l1 ⊔ l2)
mere-equiv-Prop X Y = trunc-Prop (X ≃ Y)

mere-equiv :
  {l1 l2 : Level} → UU l1 → UU l2 → UU (l1 ⊔ l2)
mere-equiv X Y = type-Prop (mere-equiv-Prop X Y)

abstract
  is-prop-mere-equiv :
    {l1 l2 : Level} (X : UU l1) (Y : UU l2) → is-prop (mere-equiv X Y)
  is-prop-mere-equiv X Y = is-prop-type-Prop (mere-equiv-Prop X Y)
```

## Properties

### Mere equivalence is reflexive

```agda
abstract
  refl-mere-equiv :
    {l1 : Level} (X : UU l1) → mere-equiv X X
  refl-mere-equiv X = unit-trunc-Prop id-equiv
```

### Mere equivalence is symmetric

```agda
abstract
  symmetric-mere-equiv :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} → mere-equiv X Y → mere-equiv Y X
  symmetric-mere-equiv {l1} {l2} {X} {Y} =
    map-universal-property-trunc-Prop
      ( mere-equiv-Prop Y X)
      ( λ e → unit-trunc-Prop (inv-equiv e))
```

### Mere equivalence is transitive

```agda
abstract
  transitive-mere-equiv :
    {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} {Z : UU l3} →
    mere-equiv X Y → mere-equiv Y Z → mere-equiv X Z
  transitive-mere-equiv {X = X} {Y} {Z} e f =
    apply-universal-property-trunc-Prop e
      ( mere-equiv-Prop X Z)
      ( λ e' →
        apply-universal-property-trunc-Prop f
          ( mere-equiv-Prop X Z)
          ( λ f' → unit-trunc-Prop (f' ∘e e')))
```

### Truncated types are closed under mere equivalence

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} 
  where
  
  is-trunc-mere-equiv : (k : 𝕋) → mere-equiv X Y → is-trunc k Y → is-trunc k X
  is-trunc-mere-equiv k e H =
     apply-universal-property-trunc-Prop
       ( e)
       ( is-trunc-Prop k X)
       ( λ f → is-trunc-equiv k Y f H)

  is-trunc-mere-equiv' : (k : 𝕋) → mere-equiv X Y → is-trunc k X → is-trunc k Y
  is-trunc-mere-equiv' k e H =
    apply-universal-property-trunc-Prop
      ( e)
      ( is-trunc-Prop k Y)
      ( λ f → is-trunc-equiv' k X f H)
```

### Sets are closed under mere equivalence

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} 
  where
  
  is-set-mere-equiv : mere-equiv X Y → is-set Y → is-set X
  is-set-mere-equiv = is-trunc-mere-equiv zero-𝕋

  is-set-mere-equiv' : mere-equiv X Y → is-set X → is-set Y
  is-set-mere-equiv' = is-trunc-mere-equiv' zero-𝕋
```

### Types with decidable equality are closed under mere equivalences

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where
  
  has-decidable-equality-mere-equiv :
    mere-equiv X Y → has-decidable-equality Y → has-decidable-equality X
  has-decidable-equality-mere-equiv e d =
    apply-universal-property-trunc-Prop e
      ( has-decidable-equality-Prop X)
      ( λ f → has-decidable-equality-equiv f d)

  has-decidable-equality-mere-equiv' :
    mere-equiv X Y → has-decidable-equality X → has-decidable-equality Y
  has-decidable-equality-mere-equiv' e d =
    apply-universal-property-trunc-Prop e
      ( has-decidable-equality-Prop Y)
      ( λ f → has-decidable-equality-equiv' f d)
```

### Mere equivalence implies mere equality

```agda
abstract
  mere-eq-mere-equiv :
    {l : Level} {A B : UU l} → mere-equiv A B → mere-eq A B
  mere-eq-mere-equiv {l} {A} {B} = map-trunc-Prop (eq-equiv A B)
```
