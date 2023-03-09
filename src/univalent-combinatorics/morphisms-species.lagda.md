# Morphisms of species

```agda
module univalent-combinatorics.morphisms-species where
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
open import foundation.univalence
open import foundation.universe-levels

open import univalent-combinatorics.finite-types
open import univalent-combinatorics.species
```

</details>

### Idea

A homomorphism between two species is a pointwise family of
maps between their values.

## Definitions

### Morphisms of species

```agda
hom-species :
  {l1 l2 l3 : Level} →
  species l1 l2 → species l1 l3 → UU (lsuc l1 ⊔ l2 ⊔ l3)
hom-species {l1} F G = (X : 𝔽 l1) → F X → G X

id-hom-species : {l1 l2 : Level} → (F : species l1 l2) → hom-species F F
id-hom-species F = λ X x → x

comp-hom-species :
  {l1 l2 l3 l4 : Level}
  {F : species l1 l2} {G : species l1 l3} {H : species l1 l4} →
  hom-species G H → hom-species F G → hom-species F H
comp-hom-species f g X = (f X) ∘ (g X)
```

### Homotopies between morphisms of species

```agda
htpy-hom-species :
  {l1 l2 l3 : Level} {F : species l1 l2} {G : species l1 l3} →
  hom-species F G → hom-species F G → UU (lsuc l1 ⊔ l2 ⊔ l3)
htpy-hom-species {l1} f g = (X : 𝔽 l1) → (f X) ~ (g X)

refl-htpy-hom-species :
  {l1 l2 l3 : Level} {F : species l1 l2} {G : species l1 l3}
  (f : hom-species F G) → htpy-hom-species f f
refl-htpy-hom-species f X = refl-htpy
```

## Properties

### Homotopies characterize the identity type of morphisms of species

```agda
htpy-eq-hom-species :
  {l1 l2 l3 : Level} {F : species l1 l2} {G : species l1 l3}
  {f g : hom-species F G} →
  Id f g → htpy-hom-species f g
htpy-eq-hom-species refl X y = refl

is-contr-htpy-hom-species :
  {l1 l2 l3 : Level} {F : species l1 l2} {G : species l1 l3}
  (f : hom-species F G) → is-contr (Σ (hom-species F G) (htpy-hom-species f))
is-contr-htpy-hom-species f =
  is-contr-total-Eq-Π (λ X h → f X ~ h) (λ X → is-contr-total-htpy (f X))

is-equiv-htpy-eq-hom-species :
  {l1 l2 l3 : Level} {F : species l1 l2} {G : species l1 l3}
  (f g : hom-species F G) → is-equiv (htpy-eq-hom-species {f = f} {g = g})
is-equiv-htpy-eq-hom-species f =
  fundamental-theorem-id
    ( is-contr-htpy-hom-species f)
    ( λ g → htpy-eq-hom-species {f = f} {g = g})

eq-htpy-hom-species :
  {l1 l2 l3 : Level} {F : species l1 l2} {G : species l1 l3}
  {f g : hom-species F G} → htpy-hom-species f g → Id f g
eq-htpy-hom-species {f = f} {g = g} =
  map-inv-is-equiv (is-equiv-htpy-eq-hom-species f g)
```

### Associativity of composition

```agda
associative-comp-hom-species :
  {l1 l2 l3 l4 l5 : Level} {F : species l1 l2} {G : species l1 l3}
  {H : species l1 l4} {K : species l1 l5}
  (h : hom-species H K) (g : hom-species G H) (f : hom-species F G) →
  Id ( comp-hom-species (comp-hom-species h g) f)
     ( comp-hom-species h (comp-hom-species g f))
associative-comp-hom-species h g f = refl
```

### Unit laws of composition

```agda
left-unit-law-comp-hom-species :
  {l1 l2 l3 : Level} {F : species l1 l2} {G : species l1 l3}
  (f : hom-species F G) → Id (comp-hom-species (id-hom-species G) f) f
left-unit-law-comp-hom-species f = refl

right-unit-law-comp-hom-species :
  {l1 l2 l3 : Level} {F : species l1 l2} {G : species l1 l3}
  (f : hom-species F G) → Id (comp-hom-species f (id-hom-species F)) f
right-unit-law-comp-hom-species f = refl
```
