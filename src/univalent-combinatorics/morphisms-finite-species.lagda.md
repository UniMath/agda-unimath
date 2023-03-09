# Morphisms of finite species

```agda
module univalent-combinatorics.morphisms-finite-species where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.functions
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.finite-species
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.morphisms-species
```

</details>

## Idea

A homomorphism between two finite species is a pointwise family of maps.

## Definitions

### The type of morphisms between finite species

```agda
type-hom-finite-species :
  {l1 l2 l3 : Level} → finite-species l1 l2 → finite-species l1 l3 →
  UU (lsuc l1 ⊔ l2 ⊔ l3)
type-hom-finite-species F G =
  hom-species (species-finite-species F) (species-finite-species G)
```

### The identity momorphisms of finite species

```agda
id-hom-finite-species :
  {l1 l2 : Level} (F : finite-species l1 l2) → type-hom-finite-species F F
id-hom-finite-species F = id-hom-species (species-finite-species F)
```

### Composition of morphisms of finite species

```agda
comp-hom-finite-species :
  {l1 l2 l3 l4 : Level} (F : finite-species l1 l2) (G : finite-species l1 l3)
  (H : finite-species l1 l4) → type-hom-finite-species G H →
  type-hom-finite-species F G → type-hom-finite-species F H
comp-hom-finite-species F G H = comp-hom-species
```

### Homotopies of morphisms of finite species

```agda
htpy-hom-finite-species :
  {l1 l2 l3 : Level} (F : finite-species l1 l2) (G : finite-species l1 l3) →
  (type-hom-finite-species F G) → (type-hom-finite-species F G) →
  UU (lsuc l1 ⊔ l2 ⊔ l3)
htpy-hom-finite-species F G f g = htpy-hom-species f g

refl-htpy-hom-finite-species :
  {l1 l2 l3 : Level} (F : finite-species l1 l2) (G : finite-species l1 l3) →
  (f : type-hom-finite-species F G) → htpy-hom-finite-species F G f f
refl-htpy-hom-finite-species F G f = refl-htpy-hom-species f
```

## Properties

### Associativity of composition of homomorphisms of finite species

```agda
associative-comp-hom-finite-species :
  {l1 l2 l3 l4 l5 : Level} (F : finite-species l1 l2) (G : finite-species l1 l3)
  (H : finite-species l1 l4) (K : finite-species l1 l5)
  (h : type-hom-finite-species H K)
  (g : type-hom-finite-species G H) (f : type-hom-finite-species F G) →
  Id ( comp-hom-finite-species F G K (comp-hom-finite-species G H K h g) f)
     ( comp-hom-finite-species F H K h (comp-hom-finite-species F G H g f))
associative-comp-hom-finite-species F G H K h g f = refl
```

### The unit laws for composition of homomorphisms of finite species

```agda
left-unit-law-comp-hom-finite-species :
  {l1 l2 l3 : Level} (F : finite-species l1 l2) (G : finite-species l1 l3)
  (f : type-hom-finite-species F G) →
  Id (comp-hom-finite-species F G G (id-hom-finite-species G) f) f
left-unit-law-comp-hom-finite-species F G f = refl

right-unit-law-comp-hom-finite-species :
  {l1 l2 l3 : Level} (F : finite-species l1 l2) (G : finite-species l1 l3)
  (f : type-hom-finite-species F G) →
  Id (comp-hom-finite-species F F G f (id-hom-finite-species F)) f
right-unit-law-comp-hom-finite-species F G f = refl
```

### Characterization of the identity type of homomorphisms of finite species

```agda
htpy-eq-hom-finite-species :
  {l1 l2 l3 : Level} (F : finite-species l1 l2) (G : finite-species l1 l3)
  (f g : type-hom-finite-species F G) → Id f g → htpy-hom-finite-species F G f g
htpy-eq-hom-finite-species F G f g = htpy-eq-hom-species

is-equiv-htpy-eq-hom-finite-species :
  {l1 l2 l3 : Level} (F : finite-species l1 l2) (G : finite-species l1 l3)
  (f g : type-hom-finite-species F G) →
  is-equiv (htpy-eq-hom-finite-species F G f g)
is-equiv-htpy-eq-hom-finite-species F G f g =
  is-equiv-htpy-eq-hom-species f g

extensionality-hom-finite-species :
  {l1 l2 l3 : Level} (F : finite-species l1 l2) (G : finite-species l1 l3)
  (f g : type-hom-finite-species F G) →
  Id f g ≃ htpy-hom-finite-species F G f g
pr1 (extensionality-hom-finite-species F G f g) =
  htpy-eq-hom-finite-species F G f g
pr2 (extensionality-hom-finite-species F G f g) =
  is-equiv-htpy-eq-hom-finite-species F G f g
```

### The type of homomorphisms of finite species is a set

```agda
is-set-type-hom-finite-species :
  {l1 l2 l3 : Level} (F : finite-species l1 l2) (G : finite-species l1 l3) →
  is-set (type-hom-finite-species F G)
is-set-type-hom-finite-species F G f g =
  is-prop-equiv
    ( extensionality-hom-finite-species F G f g)
    ( is-prop-Π
      ( λ X →
      is-prop-Π
        ( λ x p q →
          is-set-is-finite (is-finite-type-𝔽 (G X)) (f X x) (g X x) p q)))

hom-finite-species :
  {l1 l2 l3 : Level} (F : finite-species l1 l2) (G : finite-species l1 l3) →
  Set (lsuc l1 ⊔ l2 ⊔ l3)
pr1 (hom-finite-species F G) = type-hom-finite-species F G
pr2 (hom-finite-species F G) = is-set-type-hom-finite-species F G
```
