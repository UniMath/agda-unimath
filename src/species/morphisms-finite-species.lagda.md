# Morphisms of finite species

```agda
module species.morphisms-finite-species where
```

<details><summary>Imports</summary>

```agda
<<<<<<< HEAD
open import foundation.dependent-pair-types
open import foundation.equivalences
=======
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.functions
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
>>>>>>> 796439c910d829eeb768284e48e75d667da1fbb3
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

<<<<<<< HEAD
open import species.morphisms-species-of-types
open import species.species-of-types
=======
open import species.species-of-finite-types
>>>>>>> 796439c910d829eeb768284e48e75d667da1fbb3

open import univalent-combinatorics.finite-types
```

</details>

## Idea

A homomorphism between two finite species is a pointwise family of maps.

## Definitions

### The type of morphisms between finite species

```agda
<<<<<<< HEAD
-- type-hom-finite-species :
--   {l1 l2 l3 : Level} → finite-species l1 l2 → finite-species l1 l3 →
--   UU (lsuc l1 ⊔ l2 ⊔ l3)
-- type-hom-finite-species F G =
--   hom-species (species-finite-species F) (species-finite-species G)
=======
type-hom-species-𝔽 :
  {l1 l2 l3 : Level} → species-𝔽 l1 l2 → species-𝔽 l1 l3 →
  UU (lsuc l1 ⊔ l2 ⊔ l3)
type-hom-species-𝔽 {l1} F G = (X : 𝔽 l1) → type-𝔽 (F X) → type-𝔽 (G X)
>>>>>>> 796439c910d829eeb768284e48e75d667da1fbb3
```

### The identity momorphisms of finite species

```agda
<<<<<<< HEAD
-- id-hom-finite-species :
--   {l1 l2 : Level} (F : finite-species l1 l2) → type-hom-finite-species F F
-- id-hom-finite-species F = id-hom-species (species-finite-species F)
=======
id-hom-species-𝔽 :
  {l1 l2 : Level} (F : species-𝔽 l1 l2) → type-hom-species-𝔽 F F
id-hom-species-𝔽 F = λ X x → x
>>>>>>> 796439c910d829eeb768284e48e75d667da1fbb3
```

### Composition of morphisms of finite species

```agda
<<<<<<< HEAD
-- comp-hom-finite-species :
--   {l1 l2 l3 l4 : Level} (F : finite-species l1 l2) (G : finite-species l1 l3)
--   (H : finite-species l1 l4) → type-hom-finite-species G H →
--   type-hom-finite-species F G → type-hom-finite-species F H
-- comp-hom-finite-species F G H = comp-hom-species
=======
comp-hom-species-𝔽 :
  {l1 l2 l3 l4 : Level} (F : species-𝔽 l1 l2) (G : species-𝔽 l1 l3)
  (H : species-𝔽 l1 l4) → type-hom-species-𝔽 G H →
  type-hom-species-𝔽 F G → type-hom-species-𝔽 F H
comp-hom-species-𝔽 F G H f g X = (f X) ∘ (g X)
>>>>>>> 796439c910d829eeb768284e48e75d667da1fbb3
```

### Homotopies of morphisms of finite species

```agda
<<<<<<< HEAD
-- htpy-hom-finite-species :
-- {l1 l2 l3 : Level} (F :finite-species l1 l2) (G : finite-species l1 l3) →
-- (type-hom-finite-species F G) → (type-hom-finite-species F G) →
-- UU (lsuc l1 ⊔ l2 ⊔ l3)
-- htpy-hom-finite-species F G f g = htpy-hom-species f g

-- refl-htpy-hom-finite-species :
-- {l1 l2 l3 : Level} (F : finite-species l1 l2) (G : finite-species l1 l3) →
-- (f : type-hom-finite-species F G) → htpy-hom-finite-species F G f f
-- refl-htpy-hom-finite-species F G f = refl-htpy-hom-species f
=======
htpy-hom-species-𝔽 :
  {l1 l2 l3 : Level} (F : species-𝔽 l1 l2) (G : species-𝔽 l1 l3) →
  (type-hom-species-𝔽 F G) → (type-hom-species-𝔽 F G) →
  UU (lsuc l1 ⊔ l2 ⊔ l3)
htpy-hom-species-𝔽 {l1} F G f g = (X : 𝔽 l1) → (f X) ~ (g X)

refl-htpy-hom-species-𝔽 :
  {l1 l2 l3 : Level} (F : species-𝔽 l1 l2) (G : species-𝔽 l1 l3) →
  (f : type-hom-species-𝔽 F G) → htpy-hom-species-𝔽 F G f f
refl-htpy-hom-species-𝔽 F G f X = refl-htpy
>>>>>>> 796439c910d829eeb768284e48e75d667da1fbb3
```

## Properties

### Associativity of composition of homomorphisms of finite species

```agda
<<<<<<< HEAD
-- associative-comp-hom-finite-species :
--   {l1 l2 l3 l4 l5 : Level} (F : finite-species l1 l2)
-- (G : finite-species l1 l3)
--   (H : finite-species l1 l4) (K : finite-species l1 l5)
--   (h : type-hom-finite-species H K)
--   (g : type-hom-finite-species G H) (f : type-hom-finite-species F G) →
--   Id ( comp-hom-finite-species F G K (comp-hom-finite-species G H K h g) f)
--      ( comp-hom-finite-species F H K h (comp-hom-finite-species F G H g f))
-- associative-comp-hom-finite-species F G H K h g f = refl
=======
associative-comp-hom-species-𝔽 :
  {l1 l2 l3 l4 l5 : Level} (F : species-𝔽 l1 l2)
  (G : species-𝔽 l1 l3) (H : species-𝔽 l1 l4) (K : species-𝔽 l1 l5)
  (h : type-hom-species-𝔽 H K)
  (g : type-hom-species-𝔽 G H) (f : type-hom-species-𝔽 F G) →
  Id ( comp-hom-species-𝔽 F G K (comp-hom-species-𝔽 G H K h g) f)
     ( comp-hom-species-𝔽 F H K h (comp-hom-species-𝔽 F G H g f))
associative-comp-hom-species-𝔽 F G H K h g f = refl
>>>>>>> 796439c910d829eeb768284e48e75d667da1fbb3
```

### The unit laws for composition of homomorphisms of finite species

```agda
<<<<<<< HEAD
-- left-unit-law-comp-hom-finite-species :
-- {l1 l2 l3 : Level} (F : finite-species l1 l2) (G : finite-species l1 l3)
-- (f : type-hom-finite-species F G) →
-- Id (comp-hom-finite-species F G G (id-hom-finite-species G) f) f
-- left-unit-law-comp-hom-finite-species F G f = refl

-- right-unit-law-comp-hom-finite-species :
-- {l1 l2 l3 : Level} (F :finite-species l1 l2) (G : finite-species l1 l3)
-- (f : type-hom-finite-species F G) →
-- Id (comp-hom-finite-species F F G f (id-hom-finite-species F)) f
-- right-unit-law-comp-hom-finite-species F G f = refl
=======
left-unit-law-comp-hom-species-𝔽 :
  {l1 l2 l3 : Level} (F : species-𝔽 l1 l2) (G : species-𝔽 l1 l3)
  (f : type-hom-species-𝔽 F G) →
  Id (comp-hom-species-𝔽 F G G (id-hom-species-𝔽 G) f) f
left-unit-law-comp-hom-species-𝔽 F G f = refl

right-unit-law-comp-hom-species-𝔽 :
  {l1 l2 l3 : Level} (F : species-𝔽 l1 l2) (G : species-𝔽 l1 l3)
  (f : type-hom-species-𝔽 F G) →
  Id (comp-hom-species-𝔽 F F G f (id-hom-species-𝔽 F)) f
right-unit-law-comp-hom-species-𝔽 F G f = refl
>>>>>>> 796439c910d829eeb768284e48e75d667da1fbb3
```

### Characterization of the identity type of homomorphisms of finite species

```agda
<<<<<<< HEAD
-- htpy-eq-hom-finite-species :
-- {l1 l2 l3 : Level} (F : finite-species l1 l2) (G : finite-species l1 l3)
-- (f g : type-hom-finite-species F G) →
-- Id f g → htpy-hom-finite-species F G f g
-- htpy-eq-hom-finite-species F G f g = htpy-eq-hom-species

-- is-equiv-htpy-eq-hom-finite-species :
-- {l1 l2 l3 : Level} (F : finite-species l1 l2) (G : finite-species l1 l3)
-- (f g : type-hom-finite-species F G) →
-- is-equiv (htpy-eq-hom-finite-species F G f g)
-- is-equiv-htpy-eq-hom-finite-species F G f g =
-- is-equiv-htpy-eq-hom-species f g

-- extensionality-hom-finite-species :
-- {l1 l2 l3 : Level} (F : finite-species l1 l2) (G : finite-species l1 l3)
-- (f g : type-hom-finite-species F G) →
-- Id f g ≃ htpy-hom-finite-species F G f g
-- pr1 (extensionality-hom-finite-species F G f g) =
-- htpy-eq-hom-finite-species F G f g
-- pr2 (extensionality-hom-finite-species F G f g) =
-- is-equiv-htpy-eq-hom-finite-species F G f g
=======
htpy-eq-hom-species-𝔽 :
  {l1 l2 l3 : Level} (F : species-𝔽 l1 l2) (G : species-𝔽 l1 l3)
  (f g : type-hom-species-𝔽 F G) →
  Id f g → htpy-hom-species-𝔽 F G f g
htpy-eq-hom-species-𝔽 F G f g refl X y = refl

is-contr-htpy-hom-species-𝔽 :
  {l1 l2 l3 : Level} (F : species-𝔽 l1 l2) (G : species-𝔽 l1 l3)
  (f : type-hom-species-𝔽 F G) →
  is-contr (Σ (type-hom-species-𝔽 F G) (htpy-hom-species-𝔽 F G f))
is-contr-htpy-hom-species-𝔽 F G f =
  is-contr-total-Eq-Π (λ X h → f X ~ h) (λ X → is-contr-total-htpy (f X))

is-equiv-htpy-eq-hom-species-𝔽 :
  {l1 l2 l3 : Level} (F : species-𝔽 l1 l2) (G : species-𝔽 l1 l3)
  (f g : type-hom-species-𝔽 F G) →
   is-equiv (htpy-eq-hom-species-𝔽 F G f g)
is-equiv-htpy-eq-hom-species-𝔽 F G f =
  fundamental-theorem-id
    ( is-contr-htpy-hom-species-𝔽 F G f)
    ( λ g → htpy-eq-hom-species-𝔽 F G f g)

extensionality-hom-species-𝔽 :
  {l1 l2 l3 : Level} (F : species-𝔽 l1 l2) (G : species-𝔽 l1 l3)
  (f g : type-hom-species-𝔽 F G) →
  Id f g ≃ htpy-hom-species-𝔽 F G f g
pr1 (extensionality-hom-species-𝔽 F G f g) =
  htpy-eq-hom-species-𝔽 F G f g
pr2 (extensionality-hom-species-𝔽 F G f g) =
  is-equiv-htpy-eq-hom-species-𝔽 F G f g
>>>>>>> 796439c910d829eeb768284e48e75d667da1fbb3
```

### The type of homomorphisms of finite species is a set

<<<<<<< HEAD
````agda
-- is-set-type-hom-finite-species :
-- {l1 l2 l3 : Level} (F : finite-species l1 l2) (G : finite-species l1 l3) →
-- is-set (type-hom-finite-species F G)
-- is-set-type-hom-finite-species F G f g =
-- is-prop-equiv
-- ( extensionality-hom-finite-species F G f g)
-- ( is-prop-Π
-- ( λ X →
-- is-prop-Π
-- ( λ x p q →
-- is-set-is-finite (is-finite-type-𝔽 (G X)) (f X x) (g X x) p q)))

-- hom-finite-species :
-- {l1 l2 l3 : Level} (F : finite-species l1 l2) (G : finite-species l1 l3) →
-- Set (lsuc l1 ⊔ l2 ⊔ l3)
-- pr1 (hom-finite-species F G) = type-hom-finite-species F G
-- pr2 (hom-finite-species F G) = is-set-type-hom-finite-species F G ```
```
````
=======
```agda
is-set-type-hom-species-𝔽 :
  {l1 l2 l3 : Level} (F : species-𝔽 l1 l2) (G : species-𝔽 l1 l3) →
  is-set (type-hom-species-𝔽 F G)
is-set-type-hom-species-𝔽 F G f g =
  is-prop-equiv
    ( extensionality-hom-species-𝔽 F G f g)
    ( is-prop-Π
      ( λ X →
        is-prop-Π
          ( λ x p q →
            is-set-is-finite (is-finite-type-𝔽 (G X)) (f X x) (g X x) p q)))

hom-species-𝔽 :
  {l1 l2 l3 : Level} (F : species-𝔽 l1 l2) (G : species-𝔽 l1 l3) →
  Set (lsuc l1 ⊔ l2 ⊔ l3)
pr1 (hom-species-𝔽 F G) = type-hom-species-𝔽 F G
pr2 (hom-species-𝔽 F G) = is-set-type-hom-species-𝔽 F G
```
>>>>>>> 796439c910d829eeb768284e48e75d667da1fbb3
