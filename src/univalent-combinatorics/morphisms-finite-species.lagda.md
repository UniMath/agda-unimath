# Morphisms of finite species

```agda
{-# OPTIONS --allow-unsolved-metas --without-K --exact-split #-}

module univalent-combinatorics.morphisms-finite-species where

open import foundation-core.sets using (UU-Set; is-set)

open import foundation.universe-levels using (Level; UU; lsuc; lzero; _⊔_)

open import foundation.propositions using (is-prop-Π; is-prop-equiv)

open import foundation.identity-types using (Id; refl)

open import foundation.contractible-types using (is-contr)

open import foundation.equivalences using (is-equiv; _≃_)

open import foundation.dependent-pair-types using (pair; Σ; pr1; pr2)

open import foundation.fundamental-theorem-of-identity-types using (fundamental-theorem-id)

open import foundation.equality-dependent-function-types using (is-contr-total-Eq-Π)

open import foundation.homotopies using (_~_; is-contr-total-htpy)

open import univalent-combinatorics.finite-types using
  (𝔽; type-𝔽; is-finite-type-𝔽)

open import foundation.functions using (_∘_; id)

open import foundation-core.contractible-types using
  ( is-contr )

open import univalent-combinatorics.finite-species
open import univalent-combinatorics.morphisms-species

open import univalent-combinatorics.equality-finite-types using
  ( is-set-is-finite )

```

### Idea

A homomorphism between two finite species is a pointwise family of
maps between their values.

## Definition

```agda
type-hom-finite-species : finite-species → finite-species → UU₁
type-hom-finite-species F G = hom-species (species-finite-species F) (species-finite-species G)
```

## The identity homomorphism of finite species

```agda
id-hom-finite-species :
  (F : finite-species) → type-hom-finite-species F F
id-hom-finite-species F = id-hom-species (species-finite-species F)
```

## Composition of morphisms of finite species

```agda
comp-hom-finite-species :
  (F G H : finite-species) → (type-hom-finite-species G H) → (type-hom-finite-species F G) → (type-hom-finite-species F H)
comp-hom-finite-species F G H = comp-hom-species
```

## Associativity of composition of homomorphisms of finite species

```agda
associative-comp-hom-finite-species :
  (F G H K : finite-species) (h : type-hom-finite-species H K) (g : type-hom-finite-species G H) (f : type-hom-finite-species F G) →
  Id ( comp-hom-finite-species F G K (comp-hom-finite-species G H K h g) f)
     ( comp-hom-finite-species F H K h (comp-hom-finite-species F G H g f))
associative-comp-hom-finite-species F G H K h g f =
  associative-law-comp-hom-species f g h
```

## The left and right unit laws for composition of homomorphisms of finite species

```agda
left-unit-law-comp-hom-finite-species :
  (F G : finite-species) (f : type-hom-finite-species F G)
  → Id (comp-hom-finite-species F F G (id-hom-finite-species F) f) f
left-unit-law-comp-hom-finite-species F G f = left-unit-law-comp-hom-species (λ X z → f X z)

right-unit-law-comp-hom-finite-species :
  (F G : finite-species) (f : type-hom-finite-species F G)
  → Id (comp-hom-finite-species F G G f (id-hom-finite-species F)) f
right-unit-law-comp-hom-finite-species F G f = right-unit-law-comp-hom-species λ X z → f X (id-hom-finite-species F X z)
```

## Characterization of the identity type of homomorphisms of finite species

```agda
htpy-hom-finite-species :
  (F G : finite-species) → (type-hom-finite-species F G) → (type-hom-finite-species F G) → UU (lsuc lzero)
htpy-hom-finite-species F G f g = htpy-hom-species f g

refl-htpy-hom-finite-species :
  (F G : finite-species) (f : type-hom-finite-species F G) → htpy-hom-finite-species F G f f
refl-htpy-hom-finite-species F G f = refl-htpy-hom-species f

htpy-eq-hom-finite-species :
  (F G : finite-species) (f g : type-hom-finite-species F G) →
  Id f g → htpy-hom-finite-species F G f g
htpy-eq-hom-finite-species F G f g = htpy-eq-hom-species

is-equiv-htpy-eq-hom-finite-species :
  (F G : finite-species) (f g : type-hom-finite-species F G) →
  is-equiv (htpy-eq-hom-finite-species F G f g)
is-equiv-htpy-eq-hom-finite-species F G f g =
  is-equiv-htpy-eq-hom-species f g

extensionality-hom-finite-species :
  (F G : finite-species) (f g : type-hom-finite-species F G) →
  Id f g ≃ htpy-hom-finite-species F G f g
pr1 (extensionality-hom-finite-species F G f g) =
  htpy-eq-hom-finite-species F G f g
pr2 (extensionality-hom-finite-species F G f g) =
  is-equiv-htpy-eq-hom-finite-species F G f g
```

## The type of homomorphisms of finite species is a set

```agda
is-set-type-hom-finite-species :
  (F G : finite-species) → is-set (type-hom-finite-species F G)
is-set-type-hom-finite-species F G f g =
  is-prop-equiv
    ( extensionality-hom-finite-species F G f g)
    ( is-prop-Π (λ X → is-prop-Π (λ x p q → is-set-is-finite (is-finite-type-𝔽 X) (f X x) (g X x) p q)))
     
hom-finite-species : (F G : finite-species) → UU-Set (lsuc lzero)
hom-finite-species F G = pair (type-hom-finite-species F G) (is-set-type-hom-finite-species F G)
```
