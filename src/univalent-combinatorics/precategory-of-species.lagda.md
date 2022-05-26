# The precategory of species

```agda
{-# OPTIONS --allow-unsolved-metas --without-K --exact-split #-}

module univalent-combinatorics.precategory-of-species where

open import category-theory.large-precategories using
  ( Large-Precat; obj-Large-Precat; hom-Large-Precat; comp-hom-Large-Precat;
    id-hom-Large-Precat; associative-comp-hom-Large-Precat;
    left-unit-law-comp-hom-Large-Precat; right-unit-law-comp-hom-Large-Precat)

open import foundation.universe-levels using (lsuc; _⊔_; lzero)

open import univalent-combinatorics.species using (species)

open import univalent-combinatorics.morphisms-species using
  (_→ˢ_; hom-species; _∘ˢ_; idˢ; associative-law-∘ˢ;
  left-unit-law-∘ˢ; right-unit-law-∘ˢ)

```

# Idea

Species and species morphisms form a precategory.

```agda

instance
  species-Large-Precat : Large-Precat lsuc (λ l1 l2 → lsuc lzero ⊔ l1 ⊔ l2)
  obj-Large-Precat species-Large-Precat = species
  hom-Large-Precat species-Large-Precat = hom-species
  comp-hom-Large-Precat species-Large-Precat = _∘ˢ_
  id-hom-Large-Precat species-Large-Precat {X = F} =  idˢ F
  associative-comp-hom-Large-Precat species-Large-Precat =
    λ f g h → associative-law-∘ˢ h g f
  left-unit-law-comp-hom-Large-Precat species-Large-Precat =
    λ f → left-unit-law-∘ˢ f
  right-unit-law-comp-hom-Large-Precat species-Large-Precat =
    λ f → right-unit-law-∘ˢ f



```