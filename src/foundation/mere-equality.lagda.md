---
title: Mere equality
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.mere-equality where

open import foundation.functoriality-propositional-truncation using
  ( map-trunc-Prop)
open import foundation.propositional-truncations using
  ( trunc-Prop; type-trunc-Prop; unit-trunc-Prop;
    apply-universal-property-trunc-Prop; is-prop-type-trunc-Prop)
open import foundation.reflecting-maps-equivalence-relations using
  ( reflects-Eq-Rel; reflecting-map-Eq-Rel)

open import foundation-core.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation-core.equivalence-relations using (Eq-Rel)
open import foundation-core.identity-types using (_＝_; refl; inv; _∙_; ap)
open import foundation-core.propositions using (Prop; is-prop)
open import foundation-core.sets using
  ( Set; type-Set; Id-Prop; is-set; is-set-prop-in-id)
open import foundation-core.universe-levels using (Level; UU)
```

## Idea

Two elements in a type are said to be merely equal if there is an element of the propositionally truncated identity type between them.

## Definition

```agda
module _
  {l : Level} {A : UU l}
  where
  
  mere-eq-Prop : A → A → Prop l
  mere-eq-Prop x y = trunc-Prop (x ＝ y)
  
  mere-eq : A → A → UU l
  mere-eq x y = type-trunc-Prop (x ＝ y)
  
  is-prop-mere-eq : (x y : A) → is-prop (mere-eq x y)
  is-prop-mere-eq x y = is-prop-type-trunc-Prop
```

## Properties

### Reflexivity

```agda
abstract
  refl-mere-eq :
    {l : Level} {A : UU l} {x : A} → mere-eq x x
  refl-mere-eq = unit-trunc-Prop refl
```

### Symmetry

```agda
abstract
  symm-mere-eq :
    {l : Level} {A : UU l} {x y : A} → mere-eq x y → mere-eq y x
  symm-mere-eq {x = x} {y} =
    map-trunc-Prop inv
```

### Transitivity

```agda
abstract
  trans-mere-eq :
    {l : Level} {A : UU l} {x y z : A} →
    mere-eq x y → mere-eq y z → mere-eq x z
  trans-mere-eq {x = x} {y} {z} p q =
    apply-universal-property-trunc-Prop p
      ( mere-eq-Prop x z)
      ( λ p' → map-trunc-Prop (λ q' → p' ∙ q') q)
```

### Mere equality is an equivalence relation

```agda
mere-eq-Eq-Rel : {l1 : Level} (A : UU l1) → Eq-Rel l1 A
pr1 (mere-eq-Eq-Rel A) = mere-eq-Prop
pr1 (pr2 (mere-eq-Eq-Rel A)) = refl-mere-eq
pr1 (pr2 (pr2 (mere-eq-Eq-Rel A))) = symm-mere-eq
pr2 (pr2 (pr2 (mere-eq-Eq-Rel A))) = trans-mere-eq
```

### Any map into a set reflects mere equality

```agda
module _
  {l1 l2 : Level} {A : UU l1} (X : Set l2) (f : A → type-Set X)
  where
  
  reflects-mere-eq : reflects-Eq-Rel (mere-eq-Eq-Rel A) f
  reflects-mere-eq {x} {y} r =
    apply-universal-property-trunc-Prop r
      ( Id-Prop X (f x) (f y))
      ( ap f)

  reflecting-map-mere-eq : reflecting-map-Eq-Rel (mere-eq-Eq-Rel A) (type-Set X)
  pr1 reflecting-map-mere-eq = f
  pr2 reflecting-map-mere-eq = reflects-mere-eq
```

### If mere equality maps into the identity type of `A`, then `A` is a set

```agda
is-set-mere-eq-in-id :
  {l : Level} {A : UU l} → ((x y : A) → mere-eq x y → x ＝ y) → is-set A
is-set-mere-eq-in-id =
  is-set-prop-in-id
    ( mere-eq)
    ( is-prop-mere-eq)
    ( λ x → refl-mere-eq)
```
