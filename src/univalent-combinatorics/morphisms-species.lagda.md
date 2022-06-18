---
title: Morphisms of species
---

```agda
{-# OPTIONS --allow-unsolved-metas --without-K --exact-split #-}

module univalent-combinatorics.morphisms-species where

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

### Idea

A homomorphism between two species is a pointwise family of
maps between their values.

## Definitions

### Morphisms of species

```agda
hom-species :
  {l1 l2 : Level} → species l1 → species l2 → UU (lsuc lzero ⊔ l1 ⊔ l2)
hom-species F G = (X : 𝔽) → F X → G X

id-hom-species : {l : Level} → (F : species l) → hom-species F F
id-hom-species F = λ X x → x 

comp-hom-species :
  {l1 l2 l3 : Level} {F : species l1} {G : species l2} {H : species l3} →
  hom-species G H → hom-species F G → hom-species F H
comp-hom-species f g X = (f X) ∘ (g X)
```

### Homotopies between morphisms of species

```agda
htpy-hom-species :
  {l1 l2 : Level} {F : species l1} {G : species l2} →
  hom-species F G → hom-species F G → UU (lsuc lzero ⊔ l1 ⊔ l2)
htpy-hom-species f g = (X : 𝔽) → (f X) ~ (g X)

refl-htpy-hom-species :
  {l1 l2 : Level} {F : species l1} {G : species l2} (f : hom-species F G) →
  htpy-hom-species f f
refl-htpy-hom-species f X = refl-htpy
```

## Properties

### Homotopies characterize the identity type of morphisms of species

```agda
htpy-eq-hom-species :
  {l1 l2 : Level} {F : species l1} {G : species l2} {f g : hom-species F G} →
  Id f g → htpy-hom-species f g
htpy-eq-hom-species refl X y = refl

is-contr-htpy-hom-species :
  {l1 l2 : Level} {F : species l1} {G : species l2} (f : hom-species F G) →
  is-contr (Σ (hom-species F G) (htpy-hom-species f))
is-contr-htpy-hom-species f =
  is-contr-total-Eq-Π (λ X h → f X ~ h) (λ X → is-contr-total-htpy (f X))

is-equiv-htpy-eq-hom-species :
  {l1 l2 : Level} {F : species l1} {G : species l2} (f g : hom-species F G) →
  is-equiv (htpy-eq-hom-species {f = f} {g = g})
is-equiv-htpy-eq-hom-species f =
  fundamental-theorem-id f
    ( refl-htpy-hom-species f)
    ( is-contr-htpy-hom-species f)
    ( λ g → htpy-eq-hom-species {f = f} {g = g})

eq-htpy-hom-species :
  {l1 l2 : Level} {F : species l1} {G : species l2} {f g : hom-species F G} →
  htpy-hom-species f g → Id f g 
eq-htpy-hom-species {f = f} {g = g} =
  map-inv-is-equiv (is-equiv-htpy-eq-hom-species f g)
```

### Associativity of composition

```agda
associative-comp-hom-species :
  {l1 l2 l3 l4 : Level}
  {F : species l1} {G : species l2} {H : species l3} {K : species l4}
  (h : hom-species H K) (g : hom-species G H) (f : hom-species F G) →
  Id ( comp-hom-species (comp-hom-species h g) f)
     ( comp-hom-species h (comp-hom-species g f))
associative-comp-hom-species h g f = refl
```

### Unit laws of composition

```agda
left-unit-law-comp-hom-species :
  {l1 l2 : Level} {F : species l1} {G : species l2} (f : hom-species F G) →
  Id (comp-hom-species (id-hom-species G) f) f
left-unit-law-comp-hom-species f = refl

right-unit-law-comp-hom-species :
  {l1 l2 : Level} {F : species l1} {G : species l2} (f : hom-species F G) →
  Id (comp-hom-species f (id-hom-species F)) f
right-unit-law-comp-hom-species f = refl
```
