# Propositional truncations

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.propositional-truncations where

open import foundation.contractible-types using (eq-is-contr)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.functions using (_∘_; precomp-Π; id)
open import foundation.homotopies using (_~_)
open import foundation.identity-types using (Id; tr; ap; _∙_)
open import foundation.propositions using
  ( all-elements-equal; is-prop; is-prop-all-elements-equal; UU-Prop; type-Prop;
    eq-is-prop; is-prop-type-Prop; is-prop-Π; type-hom-Prop)
open import foundation.universal-property-propositional-truncation using
  ( is-propositional-truncation; is-propositional-truncation-extension-property;
    universal-property-propositional-truncation; 
    universal-property-is-propositional-truncation;
    map-is-propositional-truncation)
open import foundation.universe-levels using (Level; UU)
```

## Idea

We have specified what it means to be a propositional truncation in the file `foundation.universal-property-propositional-truncation`. Here we postulate the existence of propositional truncations.

## Postulates

```agda
postulate type-trunc-Prop : {l : Level} → UU l → UU l

postulate unit-trunc-Prop : {l : Level} {A : UU l} → A → type-trunc-Prop A

postulate
  all-elements-equal-type-trunc-Prop :
    {l : Level} {A : UU l} → all-elements-equal (type-trunc-Prop A)

abstract
  is-prop-type-trunc-Prop : {l : Level} {A : UU l} → is-prop (type-trunc-Prop A)
  is-prop-type-trunc-Prop {l} {A} =
    is-prop-all-elements-equal all-elements-equal-type-trunc-Prop

trunc-Prop : {l : Level} → UU l → UU-Prop l
pr1 (trunc-Prop A) = type-trunc-Prop A
pr2 (trunc-Prop A) = is-prop-type-trunc-Prop
```

### The induction principle of propositional truncations

```agda
postulate
  ind-trunc-Prop' :
    {l l1 : Level} {A : UU l1} (P : type-trunc-Prop A → UU l)
    (f : (x : A) → P (unit-trunc-Prop x))
    (g : (x y : type-trunc-Prop A) (u : P x) (v : P y) →
         Id (tr P (all-elements-equal-type-trunc-Prop x y) u) v) →
    (x : type-trunc-Prop A) → P x
```

## Properties

### The condition in the induction principle is a property

```agda
abstract
  is-prop-condition-ind-trunc-Prop' :
    {l1 l2 : Level} {A : UU l1} {P : type-trunc-Prop A → UU l2} →
    ( (x y : type-trunc-Prop A) (u : P x) (v : P y) →
      Id (tr P (all-elements-equal-type-trunc-Prop x y) u) v) →
    (x : type-trunc-Prop A) → is-prop (P x)
  is-prop-condition-ind-trunc-Prop' {P = P} H x =
    is-prop-all-elements-equal
      ( λ u v →
        ( ap ( λ γ → tr P γ u)
             ( eq-is-contr (is-prop-type-trunc-Prop x x))) ∙
        ( H x x u v))
```

### Simplified form of the induction principle for propositional truncations

```agda
abstract
  ind-trunc-Prop :
    {l l1 : Level} {A : UU l1} (P : type-trunc-Prop A → UU-Prop l) →
    ((x : A) → type-Prop (P (unit-trunc-Prop x))) →
    (( y : type-trunc-Prop A) → type-Prop (P y))
  ind-trunc-Prop P f =
    ind-trunc-Prop' (type-Prop ∘ P) f
      ( λ x y u v → eq-is-prop (is-prop-type-Prop (P y))) 

  comp-trunc-Prop :
    {l l1 : Level} {A : UU l1} (P : type-trunc-Prop A → UU-Prop l) →
    ((precomp-Π unit-trunc-Prop (type-Prop ∘ P)) ∘ ind-trunc-Prop P) ~ id
  comp-trunc-Prop P h =
    eq-is-prop (is-prop-Π (λ x → is-prop-type-Prop (P (unit-trunc-Prop x))))
```

### The prostulated propositional truncations are propositional truncations

```agda
abstract
  is-propositional-truncation-trunc-Prop :
    {l1 l2 : Level} (A : UU l1) →
    is-propositional-truncation l2 (trunc-Prop A) unit-trunc-Prop
  is-propositional-truncation-trunc-Prop A =
    is-propositional-truncation-extension-property
      ( trunc-Prop A)
      ( unit-trunc-Prop)
      ( λ {l} Q → ind-trunc-Prop (λ x → Q))
```

### The postulated propositional truncations satisfy the universal property of propositional truncations

```agda
abstract
  universal-property-trunc-Prop : {l1 l2 : Level} (A : UU l1) →
    universal-property-propositional-truncation l2
      ( trunc-Prop A)
      ( unit-trunc-Prop)
  universal-property-trunc-Prop A =
    universal-property-is-propositional-truncation _
      ( trunc-Prop A)
      ( unit-trunc-Prop)
      ( is-propositional-truncation-trunc-Prop A)

abstract
  map-universal-property-trunc-Prop :
    {l1 l2 : Level} {A : UU l1} (P : UU-Prop l2) →
    (A → type-Prop P) → type-hom-Prop (trunc-Prop A) P
  map-universal-property-trunc-Prop {A = A} P f =
    map-is-propositional-truncation
      ( trunc-Prop A)
      ( unit-trunc-Prop)
      ( is-propositional-truncation-trunc-Prop A)
      ( P)
      ( f)

abstract
  apply-universal-property-trunc-Prop :
    {l1 l2 : Level} {A : UU l1} (t : type-trunc-Prop A) (P : UU-Prop l2) →
    (A → type-Prop P) → type-Prop P
  apply-universal-property-trunc-Prop t P f =
    map-universal-property-trunc-Prop P f t
```
