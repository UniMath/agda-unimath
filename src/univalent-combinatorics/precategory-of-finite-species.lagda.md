```agda
{-# OPTIONS --allow-unsolved-metas --without-K --exact-split #-}

module univalent-combinatorics.precategory-of-finite-species where

open import category-theory.large-precategories using
    (Large-Precat; obj-Large-Precat; hom-Large-Precat; comp-hom-Large-Precat;
    id-hom-Large-Precat; associative-comp-hom-Large-Precat;
    left-unit-law-comp-hom-Large-Precat; right-unit-law-comp-hom-Large-Precat)

open import foundation.universe-levels using (lsuc; _⊔_; lzero)

open import univalent-combinatorics.finite-species using (finite-species)

open import univalent-combinatorics.morphisms-finite-species using
  (hom-finite-species; comp-hom-finite-species; id-hom-finite-species;
  associative-comp-hom-finite-species; left-unit-law-comp-hom-finite-species;
  right-unit-law-comp-hom-finite-species)
```

### Idea

Finite species and homomorphisms of finite species form a precategory.

```agda
instance
  finite-species-Large-Precat : Large-Precat (λ _ → lsuc lzero) (λ _ _ → lsuc lzero)
  obj-Large-Precat finite-species-Large-Precat = λ l → finite-species
  hom-Large-Precat finite-species-Large-Precat = hom-finite-species
  comp-hom-Large-Precat finite-species-Large-Precat {X = F} {G} {H} =
    comp-hom-finite-species F G H
  id-hom-Large-Precat finite-species-Large-Precat {X = F} =
    id-hom-finite-species F
  associative-comp-hom-Large-Precat finite-species-Large-Precat {X = F} {G} {H} {K} =
    λ h g f → associative-comp-hom-finite-species F G H K h g f
  left-unit-law-comp-hom-Large-Precat finite-species-Large-Precat {X = F} {G} =
    λ f → left-unit-law-comp-hom-finite-species F G f
  right-unit-law-comp-hom-Large-Precat finite-species-Large-Precat {X = F} {G} =
    λ f → right-unit-law-comp-hom-finite-species F G f
```
