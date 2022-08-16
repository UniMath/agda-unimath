---
title: The group of integers
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module elementary-number-theory.group-of-integers where

open import elementary-number-theory.addition-integers
open import elementary-number-theory.integers
open import elementary-number-theory.natural-numbers

open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.iterating-automorphisms
open import foundation.unit-type
open import foundation.universe-levels

open import group-theory.groups
open import group-theory.homomorphisms-groups
open import group-theory.semigroups

open import structured-types.initial-pointed-type-equipped-with-automorphism
```

## Idea

The type of integers, equipped with a zero-element, addition, and negatives, forms a group.

## Definition

```agda
ℤ-Semigroup : Semigroup lzero
pr1 ℤ-Semigroup = ℤ-Set
pr1 (pr2 ℤ-Semigroup) = add-ℤ
pr2 (pr2 ℤ-Semigroup) = associative-add-ℤ

ℤ-Group : Group lzero
pr1 ℤ-Group = ℤ-Semigroup
pr1 (pr1 (pr2 ℤ-Group)) = zero-ℤ
pr1 (pr2 (pr1 (pr2 ℤ-Group))) = left-unit-law-add-ℤ
pr2 (pr2 (pr1 (pr2 ℤ-Group))) = right-unit-law-add-ℤ
pr1 (pr2 (pr2 ℤ-Group)) = neg-ℤ
pr1 (pr2 (pr2 (pr2 ℤ-Group))) = left-inverse-law-add-ℤ
pr2 (pr2 (pr2 (pr2 ℤ-Group))) = right-inverse-law-add-ℤ
```

## Properties

### For every element `g` of a group `G` there is a unique group homomorphism `f : ℤ → G` such that `f 1 ＝ g`

```agda
module _
  {l : Level} (G : Group l) (g : type-Group G)
  where

  generalized-map-hom-initial-Group : ℤ → type-Group G → type-Group G
  generalized-map-hom-initial-Group k =
    map-iterate-automorphism-ℤ k (equiv-mul-Group G g)

  associative-generalized-map-hom-initial-Group :
    (k : ℤ) (h1 h2 : type-Group G) →
    generalized-map-hom-initial-Group k (mul-Group G h1 h2) ＝
    mul-Group G (generalized-map-hom-initial-Group k h1) h2
  associative-generalized-map-hom-initial-Group (inl zero-ℕ) h1 h2 =
    inv (associative-mul-Group G (inv-Group G g) h1 h2)
  associative-generalized-map-hom-initial-Group (inl (succ-ℕ x)) h1 h2 =
    ( ap
      ( mul-Group G (inv-Group G g))
      ( associative-generalized-map-hom-initial-Group (inl x) h1 h2)) ∙
    ( inv
      ( associative-mul-Group G
        ( inv-Group G g)
        ( generalized-map-hom-initial-Group (inl x) h1)
        ( h2)))
  associative-generalized-map-hom-initial-Group (inr (inl star)) h1 h2 = refl
  associative-generalized-map-hom-initial-Group (inr (inr zero-ℕ)) h1 h2 =
    inv (associative-mul-Group G g h1 h2)
  associative-generalized-map-hom-initial-Group (inr (inr (succ-ℕ x))) h1 h2 =
    ( ap
      ( mul-Group G g)
      ( associative-generalized-map-hom-initial-Group (inr (inr x)) h1 h2)) ∙
    ( inv
      ( associative-mul-Group G g
        ( generalized-map-hom-initial-Group (inr (inr x)) h1)
        ( h2)))
  
  map-hom-initial-Group : ℤ → type-Group G
  map-hom-initial-Group k = generalized-map-hom-initial-Group k (unit-Group G)

  preserves-unit-map-hom-initial-Group :
    map-hom-initial-Group zero-ℤ ＝ unit-Group G
  preserves-unit-map-hom-initial-Group =
    preserves-point-map-ℤ-Pointed-Type-With-Aut
      ( pointed-type-with-aut-Group G g)

  preserves-mul-map-hom-initial-Group :
    (x y : ℤ) →
    ( map-hom-initial-Group (add-ℤ x y)) ＝
    ( mul-Group G (map-hom-initial-Group x) (map-hom-initial-Group y))
  preserves-mul-map-hom-initial-Group x y =
    ( iterate-automorphism-add-ℤ x y (equiv-mul-Group G g) (unit-Group G)) ∙
    ( ( ap
        ( generalized-map-hom-initial-Group x)
        ( inv (left-unit-law-Group G (map-hom-initial-Group y)))) ∙
      ( associative-generalized-map-hom-initial-Group x
        ( unit-Group G)
        ( map-hom-initial-Group y)))

  hom-initial-Group : type-hom-Group ℤ-Group G
  pr1 hom-initial-Group = map-hom-initial-Group
  pr2 hom-initial-Group = preserves-mul-map-hom-initial-Group
```
