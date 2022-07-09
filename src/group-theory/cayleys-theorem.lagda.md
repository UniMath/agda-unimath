---
title: Cayley's theorem
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module group-theory.cayleys-theorem where

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.embeddings using (is-emb)
open import foundation.equivalences using
  ( eq-htpy-equiv; htpy-eq-equiv)
open import foundation.identity-types using (inv; _∙_)
open import foundation.injective-maps using (is-injective; is-emb-is-injective)
open import foundation.universe-levels using (Level)

open import group-theory.embeddings-groups using (emb-Group)
open import group-theory.groups using
  ( Group; type-Group; set-Group; equiv-mul-Group; associative-mul-Group;
    right-unit-law-Group; unit-Group; is-set-type-Group)
open import group-theory.homomorphisms-groups using
  ( preserves-mul-Group; type-hom-Group)
open import group-theory.symmetric-groups using (symmetric-Group)
```

```agda
module _
  {l1 : Level} (G : Group l1)
  where
  
  map-Cayleys-theorem :
    type-Group G → type-Group (symmetric-Group (set-Group G))
  map-Cayleys-theorem x = equiv-mul-Group G x
  
  preserves-mul-map-Cayleys-theorem :
    preserves-mul-Group G (symmetric-Group (set-Group G)) map-Cayleys-theorem
  preserves-mul-map-Cayleys-theorem x y =
    eq-htpy-equiv (λ z → associative-mul-Group G x y z)

  hom-Cayleys-theorem : type-hom-Group G (symmetric-Group (set-Group G))
  pr1 hom-Cayleys-theorem = map-Cayleys-theorem
  pr2 hom-Cayleys-theorem = preserves-mul-map-Cayleys-theorem

  is-injective-map-Cayleys-theorem : is-injective map-Cayleys-theorem
  is-injective-map-Cayleys-theorem {x} {y} p =
    ( inv (right-unit-law-Group G x)) ∙
    ( ( htpy-eq-equiv p (unit-Group G)) ∙
      ( right-unit-law-Group G y))

  is-emb-map-Cayleys-theorem : is-emb map-Cayleys-theorem
  is-emb-map-Cayleys-theorem =
    is-emb-is-injective
      ( is-set-type-Group (symmetric-Group (set-Group G)))
      ( is-injective-map-Cayleys-theorem)

  Cayleys-theorem : emb-Group G (symmetric-Group (set-Group G))
  pr1 Cayleys-theorem = hom-Cayleys-theorem
  pr2 Cayleys-theorem = is-emb-map-Cayleys-theorem
```
