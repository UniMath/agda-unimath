```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.category-of-species where

open import category-theory.large-categories using
  ( is-category-Large-Precat; Large-Cat; precat-Large-Cat;
    is-category-Large-Cat)

open import foundation.equivalences using (map-inv-is-equiv)
open import foundation.fundamental-theorem-of-identity-types using
  ( fundamental-theorem-id)
open import foundation.identity-types using (Id)
open import foundation.universe-levels using (Level; lsuc; _⊔_)

open import univalent-combinatorics.species using (species)

open import univalent-combinatorics.precategory-of-species using (species-Large-Precat)
```