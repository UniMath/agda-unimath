# Homomorphisms of monoids

```agda
{-# OPTIONS --without-K --exact-split #-}

module group-theory.homomorphisms-monoids where

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.identity-types using (Id; refl)
open import foundation.universe-levels using (Level; UU; _⊔_)

open import group-theory.homomorphisms-semigroups using
  ( type-hom-Semigroup; map-hom-Semigroup; id-hom-Semigroup)
open import group-theory.monoids using (Monoid; semigroup-Monoid; unit-Monoid)
```

## Idea

Homomorphisms between two monoids are homomorphisms between their underlying semigroups that preserve the unit element.

## Definition

### Homomorphisms of monoids

```agda
preserves-unit-hom-Semigroup :
  { l1 l2 : Level} (M1 : Monoid l1) (M2 : Monoid l2) →
  ( type-hom-Semigroup (semigroup-Monoid M1) (semigroup-Monoid M2)) → UU l2
preserves-unit-hom-Semigroup M1 M2 f =
  Id ( map-hom-Semigroup
       ( semigroup-Monoid M1)
       ( semigroup-Monoid M2)
       ( f)
       ( unit-Monoid M1))
     ( unit-Monoid M2)

hom-Monoid :
  { l1 l2 : Level} (M1 : Monoid l1) (M2 : Monoid l2) → UU (l1 ⊔ l2)
hom-Monoid M1 M2 =
  Σ ( type-hom-Semigroup (semigroup-Monoid M1) (semigroup-Monoid M2))
    ( preserves-unit-hom-Semigroup M1 M2)
```

### The identity homomorphism of monoids

```agda
preserves-unit-id-hom-Monoid :
  { l : Level} (M : Monoid l) →
  preserves-unit-hom-Semigroup M M (id-hom-Semigroup (semigroup-Monoid M))
preserves-unit-id-hom-Monoid M = refl

id-hom-Monoid :
  {l : Level} (M : Monoid l) → hom-Monoid M M
pr1 (id-hom-Monoid M) = id-hom-Semigroup (semigroup-Monoid M)
pr2 (id-hom-Monoid M) = preserves-unit-id-hom-Monoid M
```
