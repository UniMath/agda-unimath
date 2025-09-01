# Morphisms of species of types

```agda
module species.morphisms-species-of-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import species.species-of-types
```

</details>

### Idea

A
{{#concept "homomorphism" Disambiguation="between species of types" Agda=hom-species-types}}
between two [species of types](species.species-of-types.md) is a pointwise
family of maps.

## Definitions

### Morphisms of species

```agda
hom-species-types :
  {l1 l2 l3 : Level} →
  species-types l1 l2 → species-types l1 l3 → UU (lsuc l1 ⊔ l2 ⊔ l3)
hom-species-types {l1} F G = (X : UU l1) → F X → G X

id-hom-species-types :
  {l1 l2 : Level} → (F : species-types l1 l2) → hom-species-types F F
id-hom-species-types F X = id

comp-hom-species-types :
  {l1 l2 l3 l4 : Level}
  {F : species-types l1 l2}
  {G : species-types l1 l3}
  {H : species-types l1 l4} →
  hom-species-types G H → hom-species-types F G → hom-species-types F H
comp-hom-species-types f g X = f X ∘ g X
```

### Homotopies between morphisms of species

```agda
htpy-hom-species-types :
  {l1 l2 l3 : Level} {F : species-types l1 l2} {G : species-types l1 l3} →
  hom-species-types F G → hom-species-types F G → UU (lsuc l1 ⊔ l2 ⊔ l3)
htpy-hom-species-types {l1} f g = (X : UU l1) → f X ~ g X

refl-htpy-hom-species-types :
  {l1 l2 l3 : Level} {F : species-types l1 l2} {G : species-types l1 l3}
  (f : hom-species-types F G) → htpy-hom-species-types f f
refl-htpy-hom-species-types f X = refl-htpy
```

## Properties

### Homotopies characterize the identity type of morphisms of species

```agda
htpy-eq-hom-species-types :
  {l1 l2 l3 : Level} {F : species-types l1 l2} {G : species-types l1 l3}
  {f g : hom-species-types F G} →
  f ＝ g → htpy-hom-species-types f g
htpy-eq-hom-species-types refl X y = refl

is-torsorial-htpy-hom-species-types :
  {l1 l2 l3 : Level} {F : species-types l1 l2} {G : species-types l1 l3}
  (f : hom-species-types F G) →
  is-torsorial (htpy-hom-species-types f)
is-torsorial-htpy-hom-species-types f =
  is-torsorial-Eq-Π (λ X → is-torsorial-htpy (f X))

is-equiv-htpy-eq-hom-species-types :
  {l1 l2 l3 : Level} {F : species-types l1 l2} {G : species-types l1 l3}
  (f g : hom-species-types F G) →
  is-equiv (htpy-eq-hom-species-types {f = f} {g = g})
is-equiv-htpy-eq-hom-species-types f =
  fundamental-theorem-id
    ( is-torsorial-htpy-hom-species-types f)
    ( λ g → htpy-eq-hom-species-types {f = f} {g = g})

eq-htpy-hom-species-types :
  {l1 l2 l3 : Level} {F : species-types l1 l2} {G : species-types l1 l3}
  {f g : hom-species-types F G} → htpy-hom-species-types f g → f ＝ g
eq-htpy-hom-species-types {f = f} {g = g} =
  map-inv-is-equiv (is-equiv-htpy-eq-hom-species-types f g)
```

### Associativity of composition

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {F : species-types l1 l2} {G : species-types l1 l3}
  {H : species-types l1 l4} {K : species-types l1 l5}
  (h : hom-species-types H K)
  (g : hom-species-types G H)
  (f : hom-species-types F G)
  where

  associative-comp-hom-species-types :
    comp-hom-species-types (comp-hom-species-types h g) f ＝
    comp-hom-species-types h (comp-hom-species-types g f)
  associative-comp-hom-species-types = refl
```

### Unit laws of composition

```agda
left-unit-law-comp-hom-species-types :
  {l1 l2 l3 : Level} {F : species-types l1 l2} {G : species-types l1 l3}
  (f : hom-species-types F G) →
  Id (comp-hom-species-types (id-hom-species-types G) f) f
left-unit-law-comp-hom-species-types f = refl

right-unit-law-comp-hom-species-types :
  {l1 l2 l3 : Level} {F : species-types l1 l2} {G : species-types l1 l3}
  (f : hom-species-types F G) →
  Id (comp-hom-species-types f (id-hom-species-types F)) f
right-unit-law-comp-hom-species-types f = refl
```
