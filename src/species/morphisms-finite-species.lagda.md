# Morphisms of finite species

```agda
module species.morphisms-finite-species where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import species.species-of-finite-types

open import univalent-combinatorics.finite-types
```

</details>

## Idea

A
{{#concept "homomorphism" Disambiguation="between finite species" Agda=hom-finite-species}}
between two [finite species](species.species-of-finite-types.md) is a pointwise
family of maps.

## Definitions

### The type of morphisms between finite species

```agda
hom-finite-species :
  {l1 l2 l3 : Level} → finite-species l1 l2 → finite-species l1 l3 →
  UU (lsuc l1 ⊔ l2 ⊔ l3)
hom-finite-species {l1} F G =
  (X : Finite-Type l1) → type-Finite-Type (F X) → type-Finite-Type (G X)
```

### The identity morphisms of finite species

```agda
id-hom-finite-species :
  {l1 l2 : Level} (F : finite-species l1 l2) → hom-finite-species F F
id-hom-finite-species F X = id
```

### Composition of morphisms of finite species

```agda
comp-hom-finite-species :
  {l1 l2 l3 l4 : Level} (F : finite-species l1 l2) (G : finite-species l1 l3)
  (H : finite-species l1 l4) → hom-finite-species G H →
  hom-finite-species F G → hom-finite-species F H
comp-hom-finite-species F G H f g X = f X ∘ g X
```

### Homotopies of morphisms of finite species

```agda
htpy-hom-finite-species :
  {l1 l2 l3 : Level} (F : finite-species l1 l2) (G : finite-species l1 l3) →
  (hom-finite-species F G) → (hom-finite-species F G) →
  UU (lsuc l1 ⊔ l2 ⊔ l3)
htpy-hom-finite-species {l1} F G f g = (X : Finite-Type l1) → f X ~ g X

refl-htpy-hom-finite-species :
  {l1 l2 l3 : Level} (F : finite-species l1 l2) (G : finite-species l1 l3) →
  (f : hom-finite-species F G) → htpy-hom-finite-species F G f f
refl-htpy-hom-finite-species F G f X = refl-htpy
```

## Properties

### Associativity of composition of homomorphisms of finite species

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (F : finite-species l1 l2) (G : finite-species l1 l3)
  (H : finite-species l1 l4) (K : finite-species l1 l5)
  where

  associative-comp-hom-finite-species :
    (h : hom-finite-species H K)
    (g : hom-finite-species G H)
    (f : hom-finite-species F G) →
    comp-hom-finite-species F G K (comp-hom-finite-species G H K h g) f ＝
    comp-hom-finite-species F H K h (comp-hom-finite-species F G H g f)
  associative-comp-hom-finite-species h g f = refl
```

### The unit laws for composition of homomorphisms of finite species

```agda
left-unit-law-comp-hom-finite-species :
  {l1 l2 l3 : Level} (F : finite-species l1 l2) (G : finite-species l1 l3)
  (f : hom-finite-species F G) →
  Id (comp-hom-finite-species F G G (id-hom-finite-species G) f) f
left-unit-law-comp-hom-finite-species F G f = refl

right-unit-law-comp-hom-finite-species :
  {l1 l2 l3 : Level} (F : finite-species l1 l2) (G : finite-species l1 l3)
  (f : hom-finite-species F G) →
  Id (comp-hom-finite-species F F G f (id-hom-finite-species F)) f
right-unit-law-comp-hom-finite-species F G f = refl
```

### Characterization of the identity type of homomorphisms of finite species

```agda
htpy-eq-hom-finite-species :
  {l1 l2 l3 : Level} (F : finite-species l1 l2) (G : finite-species l1 l3)
  (f g : hom-finite-species F G) →
  Id f g → htpy-hom-finite-species F G f g
htpy-eq-hom-finite-species F G f g refl X y = refl

is-torsorial-htpy-hom-finite-species :
  {l1 l2 l3 : Level} (F : finite-species l1 l2) (G : finite-species l1 l3)
  (f : hom-finite-species F G) → is-torsorial (htpy-hom-finite-species F G f)
is-torsorial-htpy-hom-finite-species F G f =
  is-torsorial-Eq-Π (λ X → is-torsorial-htpy (f X))

is-equiv-htpy-eq-hom-finite-species :
  {l1 l2 l3 : Level} (F : finite-species l1 l2) (G : finite-species l1 l3)
  (f g : hom-finite-species F G) →
    is-equiv (htpy-eq-hom-finite-species F G f g)
is-equiv-htpy-eq-hom-finite-species F G f =
  fundamental-theorem-id
    ( is-torsorial-htpy-hom-finite-species F G f)
    ( λ g → htpy-eq-hom-finite-species F G f g)

extensionality-hom-finite-species :
  {l1 l2 l3 : Level} (F : finite-species l1 l2) (G : finite-species l1 l3)
  (f g : hom-finite-species F G) →
  (f ＝ g) ≃ htpy-hom-finite-species F G f g
pr1 (extensionality-hom-finite-species F G f g) =
  htpy-eq-hom-finite-species F G f g
pr2 (extensionality-hom-finite-species F G f g) =
  is-equiv-htpy-eq-hom-finite-species F G f g
```

### The type of homomorphisms of finite species is a set

```agda
is-set-hom-finite-species :
  {l1 l2 l3 : Level} (F : finite-species l1 l2) (G : finite-species l1 l3) →
  is-set (hom-finite-species F G)
is-set-hom-finite-species F G f g =
  is-prop-equiv
    ( extensionality-hom-finite-species F G f g)
    ( is-prop-Π
      ( λ X →
        is-prop-Π
          ( λ x →
            is-set-is-finite
              ( is-finite-type-Finite-Type (G X))
              ( f X x)
              ( g X x))))

hom-set-finite-species :
  {l1 l2 l3 : Level} (F : finite-species l1 l2) (G : finite-species l1 l3) →
  Set (lsuc l1 ⊔ l2 ⊔ l3)
pr1 (hom-set-finite-species F G) = hom-finite-species F G
pr2 (hom-set-finite-species F G) = is-set-hom-finite-species F G
```
