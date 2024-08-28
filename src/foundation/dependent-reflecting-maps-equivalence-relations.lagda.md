# Dependent reflecting maps for equivalence relations

```agda
module foundation.dependent-reflecting-maps-equivalence-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.reflecting-maps-equivalence-relations
open import foundation.subtype-identity-principle
open import foundation.universe-levels

open import foundation-core.dependent-identifications
open import foundation-core.equivalence-relations
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.sets
open import foundation-core.torsorial-type-families
```

</details>

## Idea

Consider a type `A` equipped with an [equivalence relation](foundation.equivalence-relations.md) `R`, and consider a [reflecting map](foundation.reflecting-maps-equivalence-relations.md) `f : A → B` with

```text
  ρ : {x y : A} → R x y → f x ＝ f y.
```

Furthermore, consider a type family `C` over `B`. A dependent function `g : (x : A) → C (f x)` is said to be a {{#concept "dependent reflecting map" Disambiguation="equivalence relations" Agda=reflecting-map-equivalence-relation}} if we there is a [dependent identification](foundation-core.dependent-identifications.md) `dependent-identification C (ρ r) (g x) (g y)` for every `r : R x y` and every `x y : A`.

## Definitions

### The predicate of being a dependent reflecting map

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  {B : UU l3} (f : reflecting-map-equivalence-relation R B)
  where

  is-dependent-reflecting-map-equivalence-relation :
    {l4 : Level} (C : B → UU l4) →
    ((x : A) → C (map-reflecting-map-equivalence-relation R f x)) →
    UU (l1 ⊔ l2 ⊔ l4)
  is-dependent-reflecting-map-equivalence-relation C g =
    {x y : A} (r : sim-equivalence-relation R x y) →
    dependent-identification C
      ( reflects-map-reflecting-map-equivalence-relation R f r)
      ( g x)
      ( g y)
```

### Dependent reflecting maps

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  {B : UU l3} (f : reflecting-map-equivalence-relation R B)
  (C : B → UU l4)
  where

  dependent-reflecting-map-equivalence-relation : UU (l1 ⊔ l2 ⊔ l4)
  dependent-reflecting-map-equivalence-relation =
    Σ ( (x : A) → C (map-reflecting-map-equivalence-relation R f x))
      ( is-dependent-reflecting-map-equivalence-relation R f C)

  map-dependent-reflecting-map-equivalence-relation :
    dependent-reflecting-map-equivalence-relation →
    (x : A) → C (map-reflecting-map-equivalence-relation R f x)
  map-dependent-reflecting-map-equivalence-relation = pr1

  reflects-map-dependent-reflecting-map-equivalence-relation :
    (g : dependent-reflecting-map-equivalence-relation) →
    is-dependent-reflecting-map-equivalence-relation R f C
      ( map-dependent-reflecting-map-equivalence-relation g)
  reflects-map-dependent-reflecting-map-equivalence-relation = pr2
```

## Properties

### Being a dependent reflecting map into a family of sets is a proposition

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  {B : UU l3} (f : reflecting-map-equivalence-relation R B)
  (C : B → Set l4)
  (g : (x : A) → type-Set (C (map-reflecting-map-equivalence-relation R f x)))
  where

  is-prop-is-dependent-reflecting-map-equivalence-relation :
    is-prop
      ( is-dependent-reflecting-map-equivalence-relation R f (type-Set ∘ C) g)
  is-prop-is-dependent-reflecting-map-equivalence-relation =
    is-prop-implicit-Π
      ( λ x →
        is-prop-implicit-Π
          ( λ y → is-prop-Π (λ r → is-set-type-Set (C _) _ _)))

  is-dependent-reflecting-map-prop-equivalence-relation :
    Prop (l1 ⊔ l2 ⊔ l4)
  pr1 is-dependent-reflecting-map-prop-equivalence-relation =
    is-dependent-reflecting-map-equivalence-relation R f (type-Set ∘ C) g
  pr2 is-dependent-reflecting-map-prop-equivalence-relation =
    is-prop-is-dependent-reflecting-map-equivalence-relation    
```

### Characterizing the identity type of dependent reflecting maps into families of sets

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  {B : UU l3} (f : reflecting-map-equivalence-relation R B)
  (C : B → Set l4)
  (g : dependent-reflecting-map-equivalence-relation R f (type-Set ∘ C))
  where

  htpy-dependent-reflecting-map-equivalence-relation :
    (h : dependent-reflecting-map-equivalence-relation R f (type-Set ∘ C)) →
    UU (l1 ⊔ l4)
  htpy-dependent-reflecting-map-equivalence-relation h =
    map-dependent-reflecting-map-equivalence-relation R f (type-Set ∘ C) g ~
    map-dependent-reflecting-map-equivalence-relation R f (type-Set ∘ C) h

  refl-htpy-dependent-reflecting-map-equivalence-relation :
    htpy-dependent-reflecting-map-equivalence-relation g
  refl-htpy-dependent-reflecting-map-equivalence-relation = refl-htpy

  htpy-eq-dependent-reflecting-map-equivalence-relation :
    (h : dependent-reflecting-map-equivalence-relation R f (type-Set ∘ C)) →
    g ＝ h → htpy-dependent-reflecting-map-equivalence-relation h
  htpy-eq-dependent-reflecting-map-equivalence-relation h refl =
    refl-htpy-dependent-reflecting-map-equivalence-relation

  is-torsorial-htpy-dependent-reflecting-map-equivalence-relation :
    is-torsorial htpy-dependent-reflecting-map-equivalence-relation
  is-torsorial-htpy-dependent-reflecting-map-equivalence-relation =
    is-torsorial-Eq-subtype
      ( is-torsorial-htpy
        ( map-dependent-reflecting-map-equivalence-relation R f
          ( type-Set ∘ C)
          ( g)))
      ( is-prop-is-dependent-reflecting-map-equivalence-relation R f C)
      ( map-dependent-reflecting-map-equivalence-relation R f (type-Set ∘ C) g)
      ( refl-htpy)
      ( reflects-map-dependent-reflecting-map-equivalence-relation R f
        ( type-Set ∘ C)
        ( g))

  is-equiv-htpy-eq-dependent-reflecting-map-equivalence-relation :
    (h : dependent-reflecting-map-equivalence-relation R f (type-Set ∘ C)) →
    is-equiv (htpy-eq-dependent-reflecting-map-equivalence-relation h)
  is-equiv-htpy-eq-dependent-reflecting-map-equivalence-relation =
    fundamental-theorem-id
      is-torsorial-htpy-dependent-reflecting-map-equivalence-relation
      htpy-eq-dependent-reflecting-map-equivalence-relation

  extensionality-dependent-reflecting-map-equivalence-relation :
    (h : dependent-reflecting-map-equivalence-relation R f (type-Set ∘ C)) →
    (g ＝ h) ≃ htpy-dependent-reflecting-map-equivalence-relation h
  pr1 (extensionality-dependent-reflecting-map-equivalence-relation h) =
    htpy-eq-dependent-reflecting-map-equivalence-relation h
  pr2 (extensionality-dependent-reflecting-map-equivalence-relation h) =
    is-equiv-htpy-eq-dependent-reflecting-map-equivalence-relation h

  eq-htpy-dependent-reflecting-map-equivalence-relation :
    (h : dependent-reflecting-map-equivalence-relation R f (type-Set ∘ C)) →
    htpy-dependent-reflecting-map-equivalence-relation h → g ＝ h
  eq-htpy-dependent-reflecting-map-equivalence-relation h =
    map-inv-is-equiv
      ( is-equiv-htpy-eq-dependent-reflecting-map-equivalence-relation h)
```

## See also

- [Reflecting maps](foundation.reflecting-maps-equivalence-relations.md)
