# The universal property of fibers of maps

```agda
module foundation.universal-property-fibers-of-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation.dependent-pair-types
open import foundation.dependent-universal-property-equivalences
open import foundation-core.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.subtype-identity-principle
open import foundation.universal-property-dependent-pair-types
open import foundation.universe-levels

open import foundation.families-of-equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
```

</details>

## Idea

Any map `f : A → B` induces a type family `fiber f : B → 𝒰` of
[fibers](foundation-core.fibers-of-maps.md) of `f`. By
[precomposing](foundation.precomposition-type-families.md) with `f`, we obtain
the type family `(fiber f) ∘ f : A → 𝒰`, which always has a section given by

```text
  λ a → (a , refl) : (a : A) → fiber f (f a).
```

We can uniquely characterize the family of fibers `fiber f : B → 𝒰` as the
initial type family equipped with such a section. Explicitly, the
{{#concept "universal property of the fiber" Disambiguation="of a map"}}
`fiber f : B → 𝒰` of a map `f` is that the precomposition operation

```text
  ((b : B) → fiber f b → P b) → ((a : A) → P (f a))
```

is an [equivalence](foundation-core.equivalences.md) for any type family
`P : B → 𝒰`.

This universal property is especially useful when `A` or `B` enjoy mapping out
universal properties. This lets us characterize the sections `(a : A) → P (f a)`
in terms of the mapping out properties of `A` and the descent data of `B`.

## Definition

### The canonical map used in the universal property and dependent universal property of the fibers of a map

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  (F : B → UU l3) (δ : (a : A) → F (f a))
  where

  ev-fiber :
    {l4 : Level} {P : (b : B) → F b → UU l4} →
    ((b : B) (z : F b) → P b z) → (a : A) → P (f a) (δ a)
  ev-fiber h a = h (f a) (δ a)
```

### The universal property of the fibers of a map

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  where

  universal-property-fiber :
    (f : A → B) (F : B → UU l3) (δ : (a : A) → F (f a)) → UUω
  universal-property-fiber f F δ =
    {l : Level} (P : B → UU l) → is-equiv (ev-fiber f F δ {l} {λ b _ → P b})
```

### The dependent universal property of the fibers of a map

```agda
  dependent-universal-property-fiber :
    (f : A → B) (F : B → UU l3) (δ : (a : A) → F (f a)) → UUω
  dependent-universal-property-fiber f F δ =
    {l : Level} (P : (b : B) → F b → UU l) → is-equiv (ev-fiber f F δ {l} {P})
```

## Properties

### When a product is taken over all fibers of a map, then we can equivalently take the product over the domain of that map

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  (C : (y : B) (z : fiber f y) → UU l3)
  where

  map-reduce-Π-fiber :
    ((y : B) (z : fiber f y) → C y z) → ((x : A) → C (f x) (x , refl))
  map-reduce-Π-fiber h x = h (f x) (x , refl)

  inv-map-reduce-Π-fiber :
    ((x : A) → C (f x) (x , refl)) → ((y : B) (z : fiber f y) → C y z)
  inv-map-reduce-Π-fiber h .(f x) (x , refl) = h x

  is-section-inv-map-reduce-Π-fiber :
    (map-reduce-Π-fiber ∘ inv-map-reduce-Π-fiber) ~ id
  is-section-inv-map-reduce-Π-fiber h = refl

  is-retraction-inv-map-reduce-Π-fiber' :
    (h : (y : B) (z : fiber f y) → C y z) (y : B) →
    (inv-map-reduce-Π-fiber (map-reduce-Π-fiber h) y) ~ (h y)
  is-retraction-inv-map-reduce-Π-fiber' h .(f z) (z , refl) = refl

  is-retraction-inv-map-reduce-Π-fiber :
    (inv-map-reduce-Π-fiber ∘ map-reduce-Π-fiber) ~ id
  is-retraction-inv-map-reduce-Π-fiber h =
    eq-htpy (eq-htpy ∘ is-retraction-inv-map-reduce-Π-fiber' h)

  is-equiv-map-reduce-Π-fiber : is-equiv map-reduce-Π-fiber
  is-equiv-map-reduce-Π-fiber =
    is-equiv-is-invertible
      ( inv-map-reduce-Π-fiber)
      ( is-section-inv-map-reduce-Π-fiber)
      ( is-retraction-inv-map-reduce-Π-fiber)

  reduce-Π-fiber' :
    ((y : B) (z : fiber f y) → C y z) ≃ ((x : A) → C (f x) (x , refl))
  pr1 reduce-Π-fiber' = map-reduce-Π-fiber
  pr2 reduce-Π-fiber' = is-equiv-map-reduce-Π-fiber

reduce-Π-fiber :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  (C : B → UU l3) → ((y : B) → fiber f y → C y) ≃ ((x : A) → C (f x))
reduce-Π-fiber f C = reduce-Π-fiber' f (λ y z → C y)
```

### The family of fibers has the universal property of fibers of maps

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  section-family-of-fibers :
    (a : A) → fiber f (f a)
  pr1 (section-family-of-fibers a) = a
  pr2 (section-family-of-fibers a) = refl

  equiv-up-family-of-fibers :
    {l : Level} → (P : B → UU l) →
    ((b : B) → fiber f b → P b) ≃ ((a : A) → P (f a))
  equiv-up-family-of-fibers P =
    equivalence-reasoning
      ( (b : B) → fiber f b → P b)
      ≃ ((w : Σ B (λ b → fiber f b)) → P (pr1 w))
        by equiv-ind-Σ
      ≃ ((a : A) → P (f a))
        by
          equiv-precomp-Π
            ( inv-equiv-total-fiber f)
            ( λ w → P (pr1 w))

  up-family-of-fibers :
    universal-property-fiber f (fiber f) (section-family-of-fibers)
  up-family-of-fibers P =
    is-equiv-map-equiv (equiv-up-family-of-fibers P)
```

### The family of fibers has the dependent universal property of fibers of maps

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  equiv-dependent-up-family-of-fibers :
    {l : Level} (P : (b : B) → fiber f b → UU l) →
    ( ( b : B) (z : fiber f b) → P b z) ≃
    ( ( a : A) → P (f a) (section-family-of-fibers f a))
  equiv-dependent-up-family-of-fibers P =
    equivalence-reasoning
      ( ( b : B) (z : fiber f b) → P b z)
      ≃ ((w : Σ B (λ b → fiber f b)) → P (pr1 w) (pr2 w))
        by equiv-ind-Σ
      ≃ ((a : A) → P (f a) (section-family-of-fibers f a))
        by
          equiv-precomp-Π
            ( inv-equiv-total-fiber f)
            ( λ w → P (pr1 w) (pr2 w))

  dependent-up-family-of-fibers :
    dependent-universal-property-fiber
      ( f)
      ( fiber f)
      ( section-family-of-fibers f)
  dependent-up-family-of-fibers P =
    is-equiv-map-equiv (equiv-dependent-up-family-of-fibers P)
```

### Fibers are uniquely unique

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {f : A → B} (F : B → UU l3)
  (δ : (a : A) → F (f a)) (P : B → UU l4) (γ : (a : A) → P (f a))
  where

  section-preserving-fiberwise-map-fiber : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  section-preserving-fiberwise-map-fiber =
    Σ ((b : B) → F b → P b) (λ h → ev-fiber f F δ h ~ γ)

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {f : A → B} {F : B → UU l3}
  {δ : (a : A) → F (f a)} {P : B → UU l4} {γ : (a : A) → P (f a)}
  where

  fiberwise-map-section-preserving-fiberwise-map-fiber :
    section-preserving-fiberwise-map-fiber F δ P γ → (b : B) → F b → P b
  fiberwise-map-section-preserving-fiberwise-map-fiber = pr1

  preserves-section-section-preserving-fiberwise-map-fiber :
    (w : section-preserving-fiberwise-map-fiber F δ P γ) →
    ev-fiber
      ( f)
      ( F)
      ( δ)
      ( fiberwise-map-section-preserving-fiberwise-map-fiber w) ~
    ( γ)
  preserves-section-section-preserving-fiberwise-map-fiber = pr2

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {f : A → B} {F : B → UU l3}
  {δ : (a : A) → F (f a)}
  where

  id-section-preserving-fiberwise-map-fiber :
    section-preserving-fiberwise-map-fiber F δ F δ
  pr1 id-section-preserving-fiberwise-map-fiber b = id
  pr2 id-section-preserving-fiberwise-map-fiber = refl-htpy

module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2} {f : A → B} {F : B → UU l3}
  {δ : (a : A) → F (f a)} {P : B → UU l4} {γ : (a : A) → P (f a)}
  {Q : B → UU l5} {η : (a : A) → Q (f a)}
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
  (δ : (a : A) → F (f a)) (u : universal-property-fiber f F δ)
  (P : B → UU l4) (γ : (a : A) → P (f a))
  where

  uniqueness-fiberwise-map-universal-property-fiber :
    is-contr (section-preserving-fiberwise-map-fiber F δ P γ)
  uniqueness-fiberwise-map-universal-property-fiber =
    is-contr-equiv
      ( fiber (ev-fiber f F δ) γ)
      ( equiv-tot
        ( λ h → equiv-eq-htpy))
      ( is-contr-map-is-equiv (u P) γ)

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
    (ev-fiber f F δ fiberwise-map-universal-property-fiber) ~ γ
  preserves-section-fiberwise-map-universal-property-fiber =
    preserves-section-section-preserving-fiberwise-map-fiber
      section-preserving-fiberwise-map-universal-property-fiber

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} (f : A → B) (F : B → UU l3)
  (δ : (a : A) → F (f a)) (u : universal-property-fiber f F δ)
  (P : B → UU l4) (γ : (a : A) → P (f a))
  (u' : universal-property-fiber f P γ)
  where

  dependent-comp-retraction-fiberwise-map-universal-property-fiber-universal-property-fiber :
    ( dependent-comp-section-preserving-fiberwise-map-fiber
      ( section-preserving-fiberwise-map-universal-property-fiber f P γ u' F δ)
      ( section-preserving-fiberwise-map-universal-property-fiber
        ( f)
        ( F)
        ( δ)
        ( u)
        ( P)
        ( γ))) ＝
    ( id-section-preserving-fiberwise-map-fiber)
  dependent-comp-retraction-fiberwise-map-universal-property-fiber-universal-property-fiber =
    eq-is-contr
      ( uniqueness-fiberwise-map-universal-property-fiber f F δ u F δ)

  dependent-comp-section-fiberwise-map-universal-property-fiber-universal-property-fiber :
    ( dependent-comp-section-preserving-fiberwise-map-fiber
      ( section-preserving-fiberwise-map-universal-property-fiber f F δ u P γ))
      ( section-preserving-fiberwise-map-universal-property-fiber
        ( f)
        ( P)
        ( γ)
        ( u')
        ( F)
        ( δ)) ＝
    ( id-section-preserving-fiberwise-map-fiber)
  dependent-comp-section-fiberwise-map-universal-property-fiber-universal-property-fiber =
    eq-is-contr
      ( uniqueness-fiberwise-map-universal-property-fiber f P γ u' P γ)

  is-fiberwise-retraction-fiberwise-map-universal-property-fiber-universal-property-fiber :
    (b : B) →
    ( ( fiberwise-map-universal-property-fiber f P γ u' F δ b) ∘
    ( fiberwise-map-universal-property-fiber f F δ u P γ b)) ~
    ( id)
  is-fiberwise-retraction-fiberwise-map-universal-property-fiber-universal-property-fiber
    b =
    htpy-eq
      ( htpy-eq
        ( ap
          ( pr1)
          ( dependent-comp-retraction-fiberwise-map-universal-property-fiber-universal-property-fiber))
        ( b))

  is-fiberwise-section-fiberwise-map-universal-property-fiber-universal-property-fiber :
    (b : B) →
    ( ( fiberwise-map-universal-property-fiber f F δ u P γ b) ∘
    ( fiberwise-map-universal-property-fiber f P γ u' F δ b)) ~
    ( id)
  is-fiberwise-section-fiberwise-map-universal-property-fiber-universal-property-fiber
    b =
    htpy-eq
      ( htpy-eq
        ( ap
          ( pr1)
          ( dependent-comp-section-fiberwise-map-universal-property-fiber-universal-property-fiber))
        ( b))

  is-fiberwise-equiv-fiberwise-map-universal-property-fiber-universal-property-fiber :
    is-fiberwise-equiv (fiberwise-map-universal-property-fiber f F δ u P γ)
  is-fiberwise-equiv-fiberwise-map-universal-property-fiber-universal-property-fiber
    b =
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
      ( is-fiberwise-section-fiberwise-map-universal-property-fiber-universal-property-fiber
        ( b))
      ( is-fiberwise-retraction-fiberwise-map-universal-property-fiber-universal-property-fiber
        ( b))

  uniquely-unique-fiberwise-map-universal-property-fiber :
    is-contr
      ( Σ (fiberwise-equiv F P)
        ( λ h → (ev-fiber f F δ (map-fiberwise-equiv h)) ~ γ))
  uniquely-unique-fiberwise-map-universal-property-fiber =
    is-torsorial-Eq-subtype
      ( uniqueness-fiberwise-map-universal-property-fiber f F δ u P γ)
      ( is-property-is-fiberwise-equiv)
      ( fiberwise-map-universal-property-fiber f F δ u P γ)
      ( preserves-section-fiberwise-map-universal-property-fiber f F δ u P γ)
      ( is-fiberwise-equiv-fiberwise-map-universal-property-fiber-universal-property-fiber)

  section-preserving-fiberwise-equiv-unique-fiberwise-map-universal-property-fiber :
    Σ (fiberwise-equiv F P)
      ( λ h → (ev-fiber f F δ (map-fiberwise-equiv h)) ~ γ)
  section-preserving-fiberwise-equiv-unique-fiberwise-map-universal-property-fiber =
    center uniquely-unique-fiberwise-map-universal-property-fiber

  fiberwise-equiv-unique-fiberwise-map-universal-property-fiber :
    fiberwise-equiv F P
  fiberwise-equiv-unique-fiberwise-map-universal-property-fiber =
    pr1
      ( section-preserving-fiberwise-equiv-unique-fiberwise-map-universal-property-fiber)

  preserves-section-fiberwise-equiv-unique-fiberwise-map-universal-property-fiber :
    (ev-fiber
      ( f)
      ( F)
      ( δ)
      ( map-fiberwise-equiv
        ( fiberwise-equiv-unique-fiberwise-map-universal-property-fiber))) ~
    ( γ)
  preserves-section-fiberwise-equiv-unique-fiberwise-map-universal-property-fiber =
    pr2
      ( section-preserving-fiberwise-equiv-unique-fiberwise-map-universal-property-fiber)
```
