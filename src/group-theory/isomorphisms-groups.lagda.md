# Isomorphisms of groups

```agda
{-# OPTIONS --without-K --exact-split #-}

module group-theory.isomorphisms-groups where

open import category-theory.isomorphisms-large-precategories using
  ( is-iso-Large-Precat; iso-Large-Precat; hom-iso-Large-Precat;
    is-iso-hom-iso-Large-Precat; hom-inv-iso-Large-Precat;
    is-sec-hom-inv-iso-Large-Precat; is-retr-hom-inv-iso-Large-Precat;
    id-iso-Large-Precat; iso-eq-Large-Precat; comp-iso-Large-Precat)

open import foundation.contractible-types using
  ( is-contr; is-contr-equiv'; is-contr-total-path)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using (_≃_; map-equiv; _∘e_)
open import foundation.functoriality-dependent-pair-types using (equiv-tot)
open import foundation.identity-types using (Id)
open import foundation.subtypes using (equiv-ap-inclusion-subtype)
open import foundation.universe-levels using (Level; UU; _⊔_)

open import group-theory.category-of-semigroups using
  ( extensionality-Semigroup)
open import group-theory.equivalences-semigroups using
  ( equiv-Semigroup)
open import group-theory.groups using
  ( Group; semigroup-Group; is-group-Prop)
open import group-theory.homomorphisms-groups using
  ( type-hom-Group)
open import group-theory.isomorphisms-semigroups using
  ( equiv-iso-equiv-Semigroup)
open import group-theory.precategory-of-groups using (Group-Large-Precat)
```

## Definitions

### Group isomorphisms

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2)
  where
  
  is-iso-hom-Group : type-hom-Group G H → UU (l1 ⊔ l2)
  is-iso-hom-Group = is-iso-Large-Precat Group-Large-Precat {X = G} {Y = H}

  type-iso-Group : UU (l1 ⊔ l2)
  type-iso-Group = iso-Large-Precat Group-Large-Precat G H

  hom-iso-Group : type-iso-Group → type-hom-Group G H
  hom-iso-Group = hom-iso-Large-Precat Group-Large-Precat G H

  is-iso-hom-iso-Group :
    (f : type-iso-Group) → is-iso-hom-Group (hom-iso-Group f)
  is-iso-hom-iso-Group = is-iso-hom-iso-Large-Precat Group-Large-Precat G H

  hom-inv-iso-Group : type-iso-Group → type-hom-Group H G
  hom-inv-iso-Group = hom-inv-iso-Large-Precat Group-Large-Precat G H

  equiv-Group : UU (l1 ⊔ l2)
  equiv-Group = equiv-Semigroup (semigroup-Group G) (semigroup-Group H)

  equiv-iso-equiv-Group : equiv-Group ≃ type-iso-Group
  equiv-iso-equiv-Group =
    equiv-iso-equiv-Semigroup (semigroup-Group G) (semigroup-Group H)

  iso-equiv-Group : equiv-Group → type-iso-Group
  iso-equiv-Group = map-equiv equiv-iso-equiv-Group
```

### The identity isomorphism

```agda
module _
  {l : Level} (G : Group l)
  where

  id-iso-Group : type-iso-Group G G
  id-iso-Group = id-iso-Large-Precat Group-Large-Precat {X = G}
```

## Properties

### The total space of group isomorphisms from a given group `G` is contractible

```agda
module _
  {l : Level} (G : Group l)
  where

  iso-eq-Group : (H : Group l) → Id G H → type-iso-Group G H
  iso-eq-Group = iso-eq-Large-Precat Group-Large-Precat G

  abstract
    extensionality-Group' : (H : Group l) → Id G H ≃ type-iso-Group G H
    extensionality-Group' H =
      ( extensionality-Semigroup
        ( semigroup-Group G)
        ( semigroup-Group H)) ∘e
      ( equiv-ap-inclusion-subtype is-group-Prop {s = G} {t = H})

  abstract
    is-contr-total-iso-Group : is-contr (Σ (Group l) (type-iso-Group G))
    is-contr-total-iso-Group =
      is-contr-equiv'
        ( Σ (Group l) (Id G))
        ( equiv-tot extensionality-Group')
        ( is-contr-total-path G)
```

### Group isomorphisms are stable by composition

```agda

module _
  {l1 l2 l3 : Level} (G : Group l1) (H : Group l2) (K : Group l3)
  where

  comp-iso-Group :
    type-iso-Group H K → type-iso-Group G H → type-iso-Group G K
  comp-iso-Group = comp-iso-Large-Precat Group-Large-Precat G H K
```
