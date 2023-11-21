# The Universal Property of Fibers of Maps

```agda
module foundation.universal-property-fibers-of-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cones-over-cospans
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-function-types
open import foundation.subtype-identity-principle
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-arithmetic-unit-type
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.constant-maps
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.pullbacks
open import foundation-core.universal-property-pullbacks
```

</details>

## Idea

A map `f : A → B` induces a type family `fiber f : B → UU`. By precomposing with
`f`, we have another type family `(fiber f) ∘ f : A → UU`. This latter type
family always has a section given by
`λ a → (a , refl) : (a : A) → fiber f (f a)`.

We can uniquely characterize the family of fibers `fiber f : B → UU` as the
initial type family equipped with such a section. Explicitly, `fiber f : B → UU`
is initial amoung type families `P : B → UU` equipped with sections
`(a : A) → P (f a)`. This can be packaged into an equivalence between fiberwise
maps from `fiber f` to `P` and sections of `B ∘ f`:

```text
((b : B) → fiber f b → P b) ≃ ((a : A) → P (f a))
```

This universal property is especially useful when `A` itself enjoys a mapping
out universal property. This lets us characterize the sections
`(a : A) → B (f a)`. And, in the case that `f` was defined using the mapping out
property of `A`, we may obtain an even nicer characterization.

For example, if we take `A` to be `unit` and the map `f : unit → B` to be
defined by a point `b₀ : B` and the universal property of `unit`, we have

```text
((b : B) → fiber f b → P b) ≃ ((t : unit) → P (f t)) ≃ ((t : unit) → P b₀) ≃ P b₀
```

which essentialy tells us `fiber f : B → UU` has the same universal property as
`Id b₀ : B → UU`.

### Temporary lemmas

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  {D : A → UU l4}
  where

  dependent-comp :
    ((a : A) → C a → D a) → ((a : A) → B a → C a) → (a : A) → B a → D a
  dependent-comp g f a b = g a (f a b)

```

## Definition

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  where

  ev-fiber :
    (f : A → B) (F : B → UU l3) (δ : (a : A) → F (f a)) {l4 : Level}
    (P : B → UU l4) → ((b : B) → F b → P b) → (a : A) → P (f a)
  ev-fiber f F δ P h a = h (f a) (δ a)

  universal-property-fiber :
    (l : Level) (f : A → B) (F : B → UU l3) (δ : (a : A) → F (f a)) →
    UU (l1 ⊔ l2 ⊔ l3 ⊔ lsuc l)
  universal-property-fiber l f F δ = (P : B → UU l) → is-equiv (ev-fiber f F δ P)
```

## Properties

### Fibers are uniquely unique

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {f : A → B} (F : B → UU l3)
  (δ : (a : A) → F (f a)) (P : B → UU l4) (γ : (a : A) → P (f a))
  where

  section-preserving-fiberwise-map-fiber : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  section-preserving-fiberwise-map-fiber =
    Σ ((b : B) → F b → P b) (λ h → (ev-fiber f F δ P h) ~ γ)

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {f : A → B} {F : B → UU l3}
  {δ : (a : A) → F (f a)} {P : B → UU l4} {γ : (a : A) → P (f a)}
  where

  fiberwise-map-section-preserving-fiberwise-map-fiber :
    section-preserving-fiberwise-map-fiber F δ P γ → (b : B) → F b → P b
  fiberwise-map-section-preserving-fiberwise-map-fiber = pr1

  preserves-section-section-preserving-fiberwise-map-fiber :
    (w : section-preserving-fiberwise-map-fiber F δ P γ) →
    (ev-fiber
      ( f)
      ( F)
      ( δ)
      ( P)
      ( fiberwise-map-section-preserving-fiberwise-map-fiber w)) ~
    ( γ)
  preserves-section-section-preserving-fiberwise-map-fiber = pr2

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {f : A → B} {F : B → UU l3}
  {δ : (a : A) → F (f a)}
  where
  
  id-section-preserving-fiberwise-map-fiber :
    section-preserving-fiberwise-map-fiber F δ F δ
  pr1 id-section-preserving-fiberwise-map-fiber = λ b → id
  pr2 id-section-preserving-fiberwise-map-fiber = refl-htpy

module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2} {f : A → B} {F : B → UU l3}
  {δ : (a : A) → F (f a)} {P : B → UU l4} {γ : (a : A) → P (f a)}
  {Q : B → UU l5} {η :(a : A) → Q (f a)}
  where

  dependent-comp-section-preserving-fiberwise-map-fiber :
    ( section-preserving-fiberwise-map-fiber P γ Q η) →
    ( section-preserving-fiberwise-map-fiber F δ P γ) →
    ( section-preserving-fiberwise-map-fiber F δ Q η)
  pr1 (dependent-comp-section-preserving-fiberwise-map-fiber g h) =
    dependent-comp
      ( fiberwise-map-section-preserving-fiberwise-map-fiber g)
      ( fiberwise-map-section-preserving-fiberwise-map-fiber h)
  pr2 (dependent-comp-section-preserving-fiberwise-map-fiber g h) a =
    ( ap
      ( (fiberwise-map-section-preserving-fiberwise-map-fiber g) (f a))
      ( preserves-section-section-preserving-fiberwise-map-fiber h a)) ∙
    ( preserves-section-section-preserving-fiberwise-map-fiber g a)
  
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} (f : A → B) (F : B → UU l3)
  (δ : (a : A) → F (f a)) (u : {l : Level} → universal-property-fiber l f F δ)
  (P : B → UU l4) (γ : (a : A) → P (f a))
  where
  
  uniqueness-fiberwise-map-universal-property-fiber :
    is-contr (section-preserving-fiberwise-map-fiber F δ P γ)
  uniqueness-fiberwise-map-universal-property-fiber =
    is-contr-equiv
      ( fiber (ev-fiber f F δ P) γ)
      ( equiv-tot
        ( λ h → equiv-eq-htpy))
      (  is-contr-map-is-equiv (u P) γ)

  section-preserving-fiberwise-map-universal-property-fiber :
    section-preserving-fiberwise-map-fiber F δ P γ
  section-preserving-fiberwise-map-universal-property-fiber =
    ( center uniqueness-fiberwise-map-universal-property-fiber)

  fiberwise-map-universal-property-fiber :
    (b : B) → F b → P b
  fiberwise-map-universal-property-fiber =
    fiberwise-map-section-preserving-fiberwise-map-fiber
      section-preserving-fiberwise-map-universal-property-fiber

  preserves-section-fiberwise-map-universal-property-fiber :
    (ev-fiber f F δ P fiberwise-map-universal-property-fiber) ~ γ
  preserves-section-fiberwise-map-universal-property-fiber =
    preserves-section-section-preserving-fiberwise-map-fiber
      section-preserving-fiberwise-map-universal-property-fiber

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} (f : A → B) (F : B → UU l3)
  (δ : (a : A) → F (f a)) (u : {l : Level} → universal-property-fiber l f F δ)
  (P : B → UU l4) (γ : (a : A) → P (f a)) (u' : {l : Level} → universal-property-fiber l f P γ)
  where

  dependent-comp-retraction-fiberwise-map-universal-property-fiber-universal-property-fiber :
    ( dependent-comp-section-preserving-fiberwise-map-fiber
      ( section-preserving-fiberwise-map-universal-property-fiber f P γ u' F δ)
      ( section-preserving-fiberwise-map-universal-property-fiber f F δ u P γ)) ＝
    ( id-section-preserving-fiberwise-map-fiber)
  dependent-comp-retraction-fiberwise-map-universal-property-fiber-universal-property-fiber =
    eq-is-contr
      ( uniqueness-fiberwise-map-universal-property-fiber f F δ u F δ)

  dependent-comp-section-fiberwise-map-universal-property-fiber-universal-property-fiber :
    ( dependent-comp-section-preserving-fiberwise-map-fiber
      ( section-preserving-fiberwise-map-universal-property-fiber f F δ u P γ))
      ( section-preserving-fiberwise-map-universal-property-fiber f P γ u' F δ)＝
    ( id-section-preserving-fiberwise-map-fiber)
  dependent-comp-section-fiberwise-map-universal-property-fiber-universal-property-fiber =
    eq-is-contr
      ( uniqueness-fiberwise-map-universal-property-fiber f P γ u' P γ)

  is-fiberwise-retraction-fiberwise-map-universal-property-fiber-universal-property-fiber :
    (b : B) →
    ( ( fiberwise-map-universal-property-fiber f P γ u' F δ b) ∘
    ( fiberwise-map-universal-property-fiber f F δ u P γ b)) ~
    ( id)
  is-fiberwise-retraction-fiberwise-map-universal-property-fiber-universal-property-fiber b =
    htpy-eq (htpy-eq (ap pr1 dependent-comp-retraction-fiberwise-map-universal-property-fiber-universal-property-fiber) b)

  is-fiberwise-section-fiberwise-map-universal-property-fiber-universal-property-fiber :
    (b : B) →
    ( ( fiberwise-map-universal-property-fiber f F δ u P γ b) ∘
    ( fiberwise-map-universal-property-fiber f P γ u' F δ b)) ~
    ( id)
  is-fiberwise-section-fiberwise-map-universal-property-fiber-universal-property-fiber b =
    htpy-eq (htpy-eq (ap pr1 dependent-comp-section-fiberwise-map-universal-property-fiber-universal-property-fiber) b)

  is-fiberwise-equiv-fiberwise-map-universal-property-fiber-universal-property-fiber :
    is-fiberwise-equiv (fiberwise-map-universal-property-fiber f F δ u P γ)
  is-fiberwise-equiv-fiberwise-map-universal-property-fiber-universal-property-fiber b =
    is-equiv-is-invertible
      ( fiberwise-map-section-preserving-fiberwise-map-fiber
        ( section-preserving-fiberwise-map-universal-property-fiber
          ( f)
          ( P)
          ( γ)
          ( u')
          ( F)
          ( δ))
        ( b))
      (is-fiberwise-section-fiberwise-map-universal-property-fiber-universal-property-fiber b)
      (is-fiberwise-retraction-fiberwise-map-universal-property-fiber-universal-property-fiber b)

  uniquely-unique-fiberwise-map-universal-property-fiber :
    is-contr
      ( Σ (fiberwise-equiv F P) (λ h → (ev-fiber f F δ P (fiberwise-map-fiberwise-equiv h)) ~ γ))
  uniquely-unique-fiberwise-map-universal-property-fiber =
    is-torsorial-Eq-subtype
      ( uniqueness-fiberwise-map-universal-property-fiber f F δ u P γ)
      ( is-property-is-fiberwise-equiv)
      ( fiberwise-map-universal-property-fiber f F δ u P γ)
      ( preserves-section-fiberwise-map-universal-property-fiber f F δ u P γ)
      ( is-fiberwise-equiv-fiberwise-map-universal-property-fiber-universal-property-fiber)

  section-preserving-fiberwise-equiv-unique-fiberwise-map-universal-property-fiber :
    Σ (fiberwise-equiv F P) (λ h → (ev-fiber f F δ P (fiberwise-map-fiberwise-equiv h)) ~ γ)
  section-preserving-fiberwise-equiv-unique-fiberwise-map-universal-property-fiber =
    center uniquely-unique-fiberwise-map-universal-property-fiber 

  fiberwise-equiv-unique-fiberwise-map-universal-property-fiber :
    fiberwise-equiv F P
  fiberwise-equiv-unique-fiberwise-map-universal-property-fiber =
    pr1 section-preserving-fiberwise-equiv-unique-fiberwise-map-universal-property-fiber

  preserves-section-fiberwise-equiv-unique-fiberwise-map-universal-property-fiber :
    (ev-fiber
      ( f)
      ( F)
      ( δ)
      ( P)
      ( fiberwise-map-fiberwise-equiv fiberwise-equiv-unique-fiberwise-map-universal-property-fiber)) ~
    ( γ)
  preserves-section-fiberwise-equiv-unique-fiberwise-map-universal-property-fiber =
    pr2 section-preserving-fiberwise-equiv-unique-fiberwise-map-universal-property-fiber
```
