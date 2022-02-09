# Propositional truncations

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.propositional-truncations where

open import foundation.cartesian-product-types using (_×_)
open import foundation.contractible-types using (eq-is-contr; center)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using (is-equiv; _≃_; map-inv-equiv)
open import foundation.functions using (_∘_; precomp-Π; id)
open import foundation.functoriality-cartesian-product-types using (map-prod)
open import foundation.homotopies using (_~_)
open import foundation.identity-types using (Id; tr; ap; _∙_)
open import foundation.propositions using
  ( all-elements-equal; is-prop; is-prop-all-elements-equal; UU-Prop; type-Prop;
    eq-is-prop; is-prop-type-Prop; is-prop-Π; type-hom-Prop; is-equiv-is-prop;
    type-equiv-Prop; prod-Prop; is-prop-prod)
open import foundation.universal-property-propositional-truncation using
  ( is-propositional-truncation; is-propositional-truncation-extension-property;
    universal-property-propositional-truncation; 
    universal-property-is-propositional-truncation;
    map-is-propositional-truncation;
    dependent-universal-property-propositional-truncation;
    dependent-universal-property-is-propositional-truncation;
    is-uniquely-unique-propositional-truncation;
    is-propositional-truncation-prod)
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

### The propositional truncation is idempotent

```agda
module _
  {l : Level} (A : UU l)
  where

  abstract
    map-idempotent-trunc-Prop :
      type-trunc-Prop (type-trunc-Prop A) → type-trunc-Prop A
    map-idempotent-trunc-Prop =
      map-universal-property-trunc-Prop (trunc-Prop A) id

  abstract
    is-equiv-map-idempotent-trunc-Prop : is-equiv map-idempotent-trunc-Prop
    is-equiv-map-idempotent-trunc-Prop =
      is-equiv-is-prop
        ( is-prop-type-trunc-Prop)
        ( is-prop-type-trunc-Prop)
        ( unit-trunc-Prop)

  idempotent-trunc-Prop :
    type-trunc-Prop (type-trunc-Prop A) ≃ type-trunc-Prop A
  pr1 idempotent-trunc-Prop = map-idempotent-trunc-Prop
  pr2 idempotent-trunc-Prop = is-equiv-map-idempotent-trunc-Prop

  abstract
    is-equiv-map-inv-idempotent-trunc-Prop :
      is-equiv (unit-trunc-Prop {A = type-trunc-Prop A})
    is-equiv-map-inv-idempotent-trunc-Prop =
      is-equiv-is-prop
        ( is-prop-type-trunc-Prop)
        ( is-prop-type-trunc-Prop)
        ( map-idempotent-trunc-Prop)

  inv-idempotent-trunc-Prop :
    type-trunc-Prop A ≃ type-trunc-Prop (type-trunc-Prop A)
  pr1 inv-idempotent-trunc-Prop = unit-trunc-Prop
  pr2 inv-idempotent-trunc-Prop = is-equiv-map-inv-idempotent-trunc-Prop
```

### Propositional truncations satisfy the dependent universal property of the propositional truncation

```agda
abstract
  dependent-universal-property-trunc-Prop :
    {l1 : Level} {A : UU l1} {l : Level} →
      dependent-universal-property-propositional-truncation l
      ( trunc-Prop A)
      ( unit-trunc-Prop)
  dependent-universal-property-trunc-Prop {A = A} =
    dependent-universal-property-is-propositional-truncation
      ( trunc-Prop A)
      ( unit-trunc-Prop)
      ( is-propositional-truncation-trunc-Prop A)

module _
  {l1 l2 : Level} {A : UU l1} (P : type-trunc-Prop A → UU-Prop l2)
  where
  
  equiv-dependent-universal-property-trunc-Prop :
    ((y : type-trunc-Prop A) → type-Prop (P y)) ≃
    ((x : A) → type-Prop (P (unit-trunc-Prop x)))
  pr1 equiv-dependent-universal-property-trunc-Prop =
    precomp-Π unit-trunc-Prop (type-Prop ∘ P)
  pr2 equiv-dependent-universal-property-trunc-Prop =
    dependent-universal-property-trunc-Prop P

  apply-dependent-universal-property-trunc-Prop :
    (y : type-trunc-Prop A) → ((x : A) → type-Prop (P (unit-trunc-Prop x))) →
    type-Prop (P y)
  apply-dependent-universal-property-trunc-Prop y f =
    map-inv-equiv equiv-dependent-universal-property-trunc-Prop f y    
```

### Propositional truncations distribute over cartesian products

```agda
equiv-prod-trunc-Prop :
  {l1 l2 : Level} (A : UU l1) (A' : UU l2) →
  type-equiv-Prop
    ( trunc-Prop (A × A'))
    ( prod-Prop (trunc-Prop A) (trunc-Prop A'))
equiv-prod-trunc-Prop A A' =
  pr1
    ( center
      ( is-uniquely-unique-propositional-truncation
        ( trunc-Prop (A × A'))
        ( prod-Prop (trunc-Prop A) (trunc-Prop A'))
        ( unit-trunc-Prop)
        ( map-prod unit-trunc-Prop unit-trunc-Prop)
        ( is-propositional-truncation-trunc-Prop (A × A'))
        ( is-propositional-truncation-prod
          ( trunc-Prop A)
          ( unit-trunc-Prop)
          ( trunc-Prop A')
          ( unit-trunc-Prop)
          ( is-propositional-truncation-trunc-Prop A)
          ( is-propositional-truncation-trunc-Prop A'))))

map-distributive-trunc-prod-Prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  type-trunc-Prop (A × B) → type-trunc-Prop A × type-trunc-Prop B
map-distributive-trunc-prod-Prop {l1} {l2} {A} {B} =
  map-universal-property-trunc-Prop
    ( pair
      ( type-trunc-Prop A × type-trunc-Prop B)
      ( is-prop-prod is-prop-type-trunc-Prop is-prop-type-trunc-Prop))
    ( map-prod unit-trunc-Prop unit-trunc-Prop)

map-inv-distributive-trunc-prod-Prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  type-trunc-Prop A × type-trunc-Prop B → type-trunc-Prop (A × B)
map-inv-distributive-trunc-prod-Prop {l1} {l2} {A} {B} t =
  map-universal-property-trunc-Prop
    ( trunc-Prop (A × B))
    ( λ x →
      map-universal-property-trunc-Prop
        ( trunc-Prop (A × B))
        ( unit-trunc-Prop ∘ (pair x))
        ( pr2 t))
    ( pr1 t)

abstract
  is-equiv-map-distributive-trunc-prod-Prop :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-equiv (map-distributive-trunc-prod-Prop {A = A} {B = B})
  is-equiv-map-distributive-trunc-prod-Prop {l1} {l2} {A} {B} =
    is-equiv-is-prop
      ( is-prop-type-trunc-Prop)
      ( is-prop-prod is-prop-type-trunc-Prop is-prop-type-trunc-Prop)
      ( map-inv-distributive-trunc-prod-Prop)

distributive-trunc-prod-Prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  type-trunc-Prop (A × B) ≃ (type-trunc-Prop A × type-trunc-Prop B)
pr1 distributive-trunc-prod-Prop = map-distributive-trunc-prod-Prop
pr2 distributive-trunc-prod-Prop = is-equiv-map-distributive-trunc-prod-Prop

abstract
  is-equiv-map-inv-distributive-trunc-prod-Prop :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-equiv (map-inv-distributive-trunc-prod-Prop {A = A} {B = B})
  is-equiv-map-inv-distributive-trunc-prod-Prop {l1} {l2} {A} {B} =
    is-equiv-is-prop
      ( is-prop-prod is-prop-type-trunc-Prop is-prop-type-trunc-Prop)
      ( is-prop-type-trunc-Prop)
      ( map-distributive-trunc-prod-Prop)

inv-distributive-trunc-prod-Prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  ( type-trunc-Prop A × type-trunc-Prop B) ≃ type-trunc-Prop (A × B)
pr1 inv-distributive-trunc-prod-Prop = map-inv-distributive-trunc-prod-Prop
pr2 inv-distributive-trunc-prod-Prop =
  is-equiv-map-inv-distributive-trunc-prod-Prop
```
