---
title: Surjective maps
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.surjective-maps where

open import foundation.sets using
  ( UU-Set; type-Set; is-set; is-set-type-Set; emb-type-Set)

open import foundation.constant-maps using (const)
open import foundation.contractible-maps using
  ( is-equiv-is-contr-map)
open import foundation.contractible-types using
  ( is-equiv-diagonal-is-contr; is-contr)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.embeddings using
  ( _↪_; map-emb; is-emb; emb-Σ; id-emb; equiv-ap-emb)
open import foundation.equivalences using
  ( is-equiv; map-inv-is-equiv; is-equiv-comp'; _≃_; map-equiv; _∘e_; inv-equiv;
    map-inv-equiv; id-equiv)
open import foundation.fibers-of-maps using
  ( fib; is-equiv-map-reduce-Π-fib; reduce-Π-fib)
open import foundation.functions using (_∘_; id)
open import foundation.functoriality-dependent-function-types using
  ( is-equiv-map-Π; equiv-map-Π)
open import foundation.functoriality-dependent-pair-types using (map-Σ)
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies using (_~_; refl-htpy; is-contr-total-htpy)
open import foundation.identity-types using (refl; _∙_; inv; equiv-tr; _＝_)
open import foundation.injective-maps using (is-injective-is-emb)
open import foundation.propositional-maps using
  ( is-prop-map-emb; is-prop-map-is-emb; fib-emb-Prop)
open import foundation.propositional-truncations using
  ( type-trunc-Prop; unit-trunc-Prop; trunc-Prop; is-prop-type-trunc-Prop;
    is-propositional-truncation-trunc-Prop;
    apply-universal-property-trunc-Prop)
open import foundation.propositions using
  ( UU-Prop; type-Prop; is-proof-irrelevant-is-prop; Π-Prop; is-prop;
    is-prop-type-Prop)
open import foundation.sections using (sec)
open import foundation.slice using
  ( hom-slice; map-hom-slice; equiv-hom-slice-fiberwise-hom;
    equiv-fiberwise-hom-hom-slice)
open import foundation.structure-identity-principle using
  ( is-contr-total-Eq-structure)
open import foundation.subtype-identity-principle using
  ( is-contr-total-Eq-subtype)
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.univalence using (is-contr-total-equiv)
open import foundation.universal-property-propositional-truncation using
  ( dependent-universal-property-propositional-truncation)
open import foundation.universe-levels using (Level; UU; _⊔_; lsuc)
```

## Idea

A map `f : A → B` is surjective if all of its fibers are inhabited.

## Definition

### Surjective maps

```agda
is-surjective-Prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → UU-Prop (l1 ⊔ l2)
is-surjective-Prop {B = B} f =
  Π-Prop B (λ b → trunc-Prop (fib f b))
    
is-surjective :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
is-surjective f = type-Prop (is-surjective-Prop f)

is-prop-is-surjective :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-prop (is-surjective f)
is-prop-is-surjective f = is-prop-type-Prop (is-surjective-Prop f)

_↠_ :
  {l1 l2 : Level} → UU l1 → UU l2 → UU (l1 ⊔ l2)
A ↠ B = Σ (A → B) is-surjective

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A ↠ B)
  where

  map-surjection : A → B
  map-surjection = pr1 f

  is-surjective-map-surjection : is-surjective map-surjection
  is-surjective-map-surjection = pr2 f
```

### The type of all surjective maps out of a type

```agda
Surjection : {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
Surjection l2 A = Σ (UU l2) (λ X → A ↠ X)

module _
  {l1 l2 : Level} {A : UU l1} (f : Surjection l2 A)
  where

  type-Surjection : UU l2
  type-Surjection = pr1 f

  surjection-Surjection : A ↠ type-Surjection
  surjection-Surjection = pr2 f

  map-Surjection : A → type-Surjection
  map-Surjection = map-surjection surjection-Surjection

  is-surjective-map-Surjection : is-surjective map-Surjection
  is-surjective-map-Surjection =
    is-surjective-map-surjection surjection-Surjection
```

### The type of all surjective maps into `k`-truncated types

```agda
Surjection-Into-Truncated-Type :
  {l1 : Level} (l2 : Level) (k : 𝕋) → UU l1 → UU (l1 ⊔ lsuc l2)
Surjection-Into-Truncated-Type l2 k A =
  Σ (Truncated-Type l2 k) (λ X → A ↠ type-Truncated-Type X)

emb-inclusion-Surjection-Into-Truncated-Type :
  {l1 : Level} (l2 : Level) (k : 𝕋) (A : UU l1) →
  Surjection-Into-Truncated-Type l2 k A ↪ Surjection l2 A
emb-inclusion-Surjection-Into-Truncated-Type l2 k A =
  emb-Σ (λ X → A ↠ X) (emb-type-Truncated-Type l2 k) (λ X → id-emb)

inclusion-Surjection-Into-Truncated-Type :
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} →
  Surjection-Into-Truncated-Type l2 k A → Surjection l2 A
inclusion-Surjection-Into-Truncated-Type {l1} {l2} {k} {A} =
  map-emb (emb-inclusion-Surjection-Into-Truncated-Type l2 k A)

module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1}
  (f : Surjection-Into-Truncated-Type l2 k A)
  where

  truncated-type-Surjection-Into-Truncated-Type : Truncated-Type l2 k
  truncated-type-Surjection-Into-Truncated-Type = pr1 f

  type-Surjection-Into-Truncated-Type : UU l2
  type-Surjection-Into-Truncated-Type =
    type-Truncated-Type truncated-type-Surjection-Into-Truncated-Type

  is-trunc-type-Surjection-Into-Truncated-Type :
    is-trunc k type-Surjection-Into-Truncated-Type
  is-trunc-type-Surjection-Into-Truncated-Type =
    is-trunc-type-Truncated-Type
      truncated-type-Surjection-Into-Truncated-Type

  surjection-Surjection-Into-Truncated-Type :
    A ↠ type-Surjection-Into-Truncated-Type
  surjection-Surjection-Into-Truncated-Type = pr2 f

  map-Surjection-Into-Truncated-Type :
    A → type-Surjection-Into-Truncated-Type
  map-Surjection-Into-Truncated-Type =
    map-surjection surjection-Surjection-Into-Truncated-Type

  is-inclusion-Surjection-Into-Truncated-Type :
    is-surjective map-Surjection-Into-Truncated-Type
  is-inclusion-Surjection-Into-Truncated-Type =
    is-surjective-map-surjection surjection-Surjection-Into-Truncated-Type
```

### The type of all surjective maps into sets

```agda
Surjection-Into-Set :
  {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
Surjection-Into-Set l2 A = Surjection-Into-Truncated-Type l2 zero-𝕋 A

emb-inclusion-Surjection-Into-Set :
  {l1 : Level} (l2 : Level) (A : UU l1) →
  Surjection-Into-Set l2 A ↪ Surjection l2 A
emb-inclusion-Surjection-Into-Set l2 A =
  emb-inclusion-Surjection-Into-Truncated-Type l2 zero-𝕋 A

inclusion-Surjection-Into-Set :
  {l1 l2 : Level} {A : UU l1} →
  Surjection-Into-Set l2 A → Surjection l2 A
inclusion-Surjection-Into-Set {l1} {l2} {A} =
  inclusion-Surjection-Into-Truncated-Type

module _
  {l1 l2 : Level} {A : UU l1} (f : Surjection-Into-Set l2 A)
  where

  set-Surjection-Into-Set : UU-Set l2
  set-Surjection-Into-Set = truncated-type-Surjection-Into-Truncated-Type f

  type-Surjection-Into-Set : UU l2
  type-Surjection-Into-Set = type-Surjection-Into-Truncated-Type f

  is-set-type-Surjection-Into-Set : is-set type-Surjection-Into-Set
  is-set-type-Surjection-Into-Set =
    is-trunc-type-Surjection-Into-Truncated-Type f

  surjection-Surjection-Into-Set : A ↠ type-Surjection-Into-Set
  surjection-Surjection-Into-Set = surjection-Surjection-Into-Truncated-Type f

  map-Surjection-Into-Set : A → type-Surjection-Into-Set
  map-Surjection-Into-Set = map-Surjection-Into-Truncated-Type f

  is-inclusion-Surjection-Into-Set : is-surjective map-Surjection-Into-Set
  is-inclusion-Surjection-Into-Set =
    is-inclusion-Surjection-Into-Truncated-Type f
```

## Properties

### Any map that has a section is surjective

```agda
abstract
  is-surjective-has-section :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
    sec f → is-surjective f
  is-surjective-has-section (pair g G) b = unit-trunc-Prop (pair (g b) (G b))
```

### Any equivalence is surjective

```agda
abstract
  is-surjective-is-equiv :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
    is-equiv f → is-surjective f
  is-surjective-is-equiv H = is-surjective-has-section (pr1 H)
```

### The dependent universal property of surjective maps

```
dependent-universal-property-surj :
  (l : Level) {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  UU ((lsuc l) ⊔ l1 ⊔ l2)
dependent-universal-property-surj l {B = B} f =
  (P : B → UU-Prop l) →
    is-equiv (λ (h : (b : B) → type-Prop (P b)) x → h (f x))

abstract
  is-surjective-dependent-universal-property-surj :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    ({l : Level} → dependent-universal-property-surj l f) →
    is-surjective f
  is-surjective-dependent-universal-property-surj f dup-surj-f =
    map-inv-is-equiv
      ( dup-surj-f (λ b → trunc-Prop (fib f b)))
      ( λ x → unit-trunc-Prop (pair x refl))

abstract
  square-dependent-universal-property-surj :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    (P : B → UU-Prop l3) →
    ( λ (h : (y : B) → type-Prop (P y)) x → h (f x)) ~
    ( ( λ h x → h (f x) (pair x refl)) ∘
      ( ( λ h y → (h y) ∘ unit-trunc-Prop) ∘
        ( λ h y → const (type-trunc-Prop (fib f y)) (type-Prop (P y)) (h y))))
  square-dependent-universal-property-surj f P = refl-htpy

  dependent-universal-property-surj-is-surjective :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-surjective f →
    ({l : Level} → dependent-universal-property-surj l f)
  dependent-universal-property-surj-is-surjective f is-surj-f P =
    is-equiv-comp'
      ( λ h x → h (f x) (pair x refl))
      ( ( λ h y → (h y) ∘ unit-trunc-Prop) ∘
        ( λ h y → const (type-trunc-Prop (fib f y)) (type-Prop (P y)) (h y)))
      ( is-equiv-comp'
        ( λ h y → (h y) ∘ unit-trunc-Prop)
        ( λ h y → const (type-trunc-Prop (fib f y)) (type-Prop (P y)) (h y))
        ( is-equiv-map-Π
          ( λ y p z → p)
          ( λ y →
            is-equiv-diagonal-is-contr
              ( is-proof-irrelevant-is-prop
                ( is-prop-type-trunc-Prop)
                ( is-surj-f y))
              ( type-Prop (P y))))
        ( is-equiv-map-Π
          ( λ b g → g ∘ unit-trunc-Prop)
          ( λ b → is-propositional-truncation-trunc-Prop (fib f b) (P b))))
      ( is-equiv-map-reduce-Π-fib f ( λ y z → type-Prop (P y)))

equiv-dependent-universal-property-surj-is-surjective :
  {l l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-surjective f → (C : B → UU-Prop l) →
  ((b : B) → type-Prop (C b)) ≃ ((a : A) → type-Prop (C (f a)))
pr1 (equiv-dependent-universal-property-surj-is-surjective f H C) h x = h (f x)
pr2 (equiv-dependent-universal-property-surj-is-surjective f H C) =
  dependent-universal-property-surj-is-surjective f H C

apply-dependent-universal-property-surj-is-surjective :
  {l l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-surjective f → (C : B → UU-Prop l) →
  ((a : A) → type-Prop (C (f a))) → ((y : B) → type-Prop (C y))
apply-dependent-universal-property-surj-is-surjective f H C =
  map-inv-equiv (equiv-dependent-universal-property-surj-is-surjective f H C)
```

### A map into a proposition is a propositional truncation if and only if it is surjective

```agda
abstract
  is-surjective-is-propositional-truncation :
    {l1 l2 : Level} {A : UU l1} {P : UU-Prop l2} (f : A → type-Prop P) →
    ( {l : Level} →
      dependent-universal-property-propositional-truncation l P f) →
    is-surjective f
  is-surjective-is-propositional-truncation f duppt-f =
    is-surjective-dependent-universal-property-surj f duppt-f

abstract
  is-propsitional-truncation-is-surjective :
    {l1 l2 : Level} {A : UU l1} {P : UU-Prop l2} (f : A → type-Prop P) →
    is-surjective f →
    {l : Level} → dependent-universal-property-propositional-truncation l P f
  is-propsitional-truncation-is-surjective f is-surj-f =
    dependent-universal-property-surj-is-surjective f is-surj-f
```

### A map that is both surjective and an embedding is an equivalence

```agda
abstract
  is-equiv-is-emb-is-surjective :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
    is-surjective f → is-emb f → is-equiv f
  is-equiv-is-emb-is-surjective {f = f} H K =
    is-equiv-is-contr-map
      ( λ y →
        is-proof-irrelevant-is-prop
          ( is-prop-map-is-emb K y)
          ( apply-universal-property-trunc-Prop
            ( H y)
            ( fib-emb-Prop (pair f K) y)
            ( id)))
```

### The composite of surjective maps is surjective

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h))
  where

  abstract
    is-surjective-comp :
      is-surjective g → is-surjective h → is-surjective f
    is-surjective-comp Sg Sh x =
      apply-universal-property-trunc-Prop
        ( Sg x)
        ( trunc-Prop (fib f x))
        ( λ { (pair b refl) →
              apply-universal-property-trunc-Prop
                ( Sh b)
                ( trunc-Prop (fib f (g b)))
                ( λ { (pair a refl) →
                  unit-trunc-Prop (pair a (H a))})})

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  {g : B → X}
  where

  abstract
    is-surjective-comp' :
      {h : A → B} → is-surjective g → is-surjective h → is-surjective (g ∘ h)
    is-surjective-comp' {h} =
      is-surjective-comp (g ∘ h) g h refl-htpy
```

### If a composite is surjective, then so is its left factor

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h))
  where

  abstract
    is-surjective-left-factor :
      is-surjective f → is-surjective g
    is-surjective-left-factor Sf x =
      apply-universal-property-trunc-Prop
        ( Sf x)
        ( trunc-Prop (fib g x))
        ( λ { (pair a refl) →
              unit-trunc-Prop (pair (h a) (inv (H a)))})

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  {g : B → X}
  where

  abstract
    is-surjective-left-factor' :
      (h : A → B) → is-surjective (g ∘ h) → is-surjective g
    is-surjective-left-factor' h =
      is-surjective-left-factor (g ∘ h) g h refl-htpy
```

### Characterization of the identity type of `A ↠ B`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A ↠ B)
  where
  
  htpy-surjection : (A ↠ B) → UU (l1 ⊔ l2)
  htpy-surjection g = map-surjection f ~ map-surjection g

  refl-htpy-surjection : htpy-surjection f
  refl-htpy-surjection = refl-htpy

  is-contr-total-htpy-surjection : is-contr (Σ (A ↠ B) htpy-surjection)
  is-contr-total-htpy-surjection =
    is-contr-total-Eq-subtype
      ( is-contr-total-htpy (map-surjection f))
      ( is-prop-is-surjective)
      ( map-surjection f)
      ( refl-htpy)
      ( is-surjective-map-surjection f)

  htpy-eq-surjection :
    (g : A ↠ B) → (f ＝ g) → htpy-surjection g
  htpy-eq-surjection .f refl = refl-htpy-surjection

  is-equiv-htpy-eq-surjection :
    (g : A ↠ B) → is-equiv (htpy-eq-surjection g)
  is-equiv-htpy-eq-surjection =
    fundamental-theorem-id is-contr-total-htpy-surjection htpy-eq-surjection

  extensionality-surjection :
    (g : A ↠ B) → (f ＝ g) ≃ htpy-surjection g
  pr1 (extensionality-surjection g) = htpy-eq-surjection g
  pr2 (extensionality-surjection g) = is-equiv-htpy-eq-surjection g

  eq-htpy-surjection : (g : A ↠ B) → htpy-surjection g → f ＝ g
  eq-htpy-surjection g =
    map-inv-equiv (extensionality-surjection g)
```

### Characterization of the identity type of `Surjection l2 A`

```agda
equiv-Surjection :
  {l1 l2 l3 : Level} {A : UU l1} →
  Surjection l2 A → Surjection l3 A → UU (l1 ⊔ l2 ⊔ l3)
equiv-Surjection f g =
  Σ ( type-Surjection f ≃ type-Surjection g)
    ( λ e → (map-equiv e ∘ map-Surjection f) ~ map-Surjection g)

module _
  {l1 l2 : Level} {A : UU l1} (f : Surjection l2 A)
  where

  id-equiv-Surjection : equiv-Surjection f f
  pr1 id-equiv-Surjection = id-equiv
  pr2 id-equiv-Surjection = refl-htpy

  is-contr-total-equiv-Surjection :
    is-contr (Σ (Surjection l2 A) (equiv-Surjection f))
  is-contr-total-equiv-Surjection =
    is-contr-total-Eq-structure
      ( λ Y g e → (map-equiv e ∘ map-Surjection f) ~ map-surjection g)
      ( is-contr-total-equiv (type-Surjection f))
      ( pair (type-Surjection f) id-equiv)
      ( is-contr-total-htpy-surjection (surjection-Surjection f))

  equiv-eq-Surjection :
    (g : Surjection l2 A) → (f ＝ g) → equiv-Surjection f g
  equiv-eq-Surjection .f refl = id-equiv-Surjection

  is-equiv-equiv-eq-Surjection :
    (g : Surjection l2 A) → is-equiv (equiv-eq-Surjection g)
  is-equiv-equiv-eq-Surjection =
    fundamental-theorem-id
      is-contr-total-equiv-Surjection
      equiv-eq-Surjection

  extensionality-Surjection :
    (g : Surjection l2 A) → (f ＝ g) ≃ equiv-Surjection f g
  pr1 (extensionality-Surjection g) = equiv-eq-Surjection g
  pr2 (extensionality-Surjection g) = is-equiv-equiv-eq-Surjection g

  eq-equiv-Surjection :
    (g : Surjection l2 A) → equiv-Surjection f g → f ＝ g
  eq-equiv-Surjection g = map-inv-equiv (extensionality-Surjection g)
```

### Characterization of the identity type of `Surjection-Into-Truncated-Type l2 k A`

```agda
equiv-Surjection-Into-Truncated-Type :
  {l1 l2 l3 : Level} {k : 𝕋} {A : UU l1} →
  Surjection-Into-Truncated-Type l2 k A →
  Surjection-Into-Truncated-Type l3 k A → UU (l1 ⊔ l2 ⊔ l3)
equiv-Surjection-Into-Truncated-Type f g =
  equiv-Surjection
    ( inclusion-Surjection-Into-Truncated-Type f)
    ( inclusion-Surjection-Into-Truncated-Type g)

module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1}
  (f : Surjection-Into-Truncated-Type l2 k A)
  where

  id-equiv-Surjection-Into-Truncated-Type :
    equiv-Surjection-Into-Truncated-Type f f
  id-equiv-Surjection-Into-Truncated-Type =
    id-equiv-Surjection (inclusion-Surjection-Into-Truncated-Type f)

  extensionality-Surjection-Into-Truncated-Type :
    (g : Surjection-Into-Truncated-Type l2 k A) →
    (f ＝ g) ≃ equiv-Surjection-Into-Truncated-Type f g
  extensionality-Surjection-Into-Truncated-Type g =
    ( extensionality-Surjection
      ( inclusion-Surjection-Into-Truncated-Type f)
      ( inclusion-Surjection-Into-Truncated-Type g)) ∘e
    ( equiv-ap-emb (emb-inclusion-Surjection-Into-Truncated-Type l2 k A))

  equiv-eq-Surjection-Into-Truncated-Type :
    (g : Surjection-Into-Truncated-Type l2 k A) →
    (f ＝ g) → equiv-Surjection-Into-Truncated-Type f g
  equiv-eq-Surjection-Into-Truncated-Type g =
    map-equiv (extensionality-Surjection-Into-Truncated-Type g)

  refl-equiv-eq-Surjection-Into-Truncated-Type :
    equiv-eq-Surjection-Into-Truncated-Type f refl ＝
    id-equiv-Surjection-Into-Truncated-Type
  refl-equiv-eq-Surjection-Into-Truncated-Type = refl

  eq-equiv-Surjection-Into-Truncated-Type :
    (g : Surjection-Into-Truncated-Type l2 k A) →
    equiv-Surjection-Into-Truncated-Type f g → f ＝ g
  eq-equiv-Surjection-Into-Truncated-Type g =
    map-inv-equiv (extensionality-Surjection-Into-Truncated-Type g)
```

### Characterization of the identity type of `Surjection-Into-Set l2 A`

```agda
equiv-Surjection-Into-Set :
  {l1 l2 l3 : Level} {A : UU l1} → Surjection-Into-Set l2 A →
  Surjection-Into-Set l3 A → UU (l1 ⊔ l2 ⊔ l3)
equiv-Surjection-Into-Set = equiv-Surjection-Into-Truncated-Type

id-equiv-Surjection-Into-Set :
  {l1 l2 : Level} {A : UU l1} (f : Surjection-Into-Set l2 A) →
  equiv-Surjection-Into-Set f f
id-equiv-Surjection-Into-Set = id-equiv-Surjection-Into-Truncated-Type

extensionality-Surjection-Into-Set :
  {l1 l2 : Level} {A : UU l1} (f g : Surjection-Into-Set l2 A) →
  (f ＝ g) ≃ equiv-Surjection-Into-Set f g
extensionality-Surjection-Into-Set =
  extensionality-Surjection-Into-Truncated-Type

equiv-eq-Surjection-Into-Set :
  {l1 l2 : Level} {A : UU l1} (f g : Surjection-Into-Set l2 A) →
  (f ＝ g) → equiv-Surjection-Into-Set f g
equiv-eq-Surjection-Into-Set = equiv-eq-Surjection-Into-Truncated-Type

refl-equiv-eq-Surjection-Into-Set :
  {l1 l2 : Level} {A : UU l1} (f : Surjection-Into-Set l2 A) →
  equiv-eq-Surjection-Into-Set f f refl ＝
  id-equiv-Surjection-Into-Set f
refl-equiv-eq-Surjection-Into-Set = refl-equiv-eq-Surjection-Into-Truncated-Type

eq-equiv-Surjection-Into-Set :
  {l1 l2 : Level} {A : UU l1} (f g : Surjection-Into-Set l2 A) →
  equiv-Surjection-Into-Set f g → f ＝ g
eq-equiv-Surjection-Into-Set = eq-equiv-Surjection-Into-Truncated-Type
```
