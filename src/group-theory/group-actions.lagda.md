---
title: Group actions
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module group-theory.group-actions where

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using ( _≃_; map-equiv)
open import foundation.function-extensionality using (htpy-eq)
open import foundation.functions using (id)
open import foundation.homotopies using (_~_)
open import foundation.identity-types using (Id; ap; inv; _∙_; refl)
open import foundation.sets using (Set; type-Set; is-set; is-set-type-Set)
open import foundation.universe-levels using (Level; UU; _⊔_; lsuc)

open import group-theory.groups using
  ( Group; type-Group; unit-Group; mul-Group; inv-Group; left-inverse-law-mul-Group;
    set-Group; equiv-mul-Group; associative-mul-Group)
open import group-theory.homomorphisms-groups using
  ( type-hom-Group; map-hom-Group; preserves-unit-hom-Group;
    preserves-mul-hom-Group)
open import group-theory.symmetric-groups using (symmetric-Group)
```

## Idea

A action of a group `G` on a set `X` is a group homomorphism from `G` into `symmetric-Group X`.

## Definition

```agda
module _
  {l1 : Level} (G : Group l1)
  where

  Abstract-Group-Action : (l : Level) → UU (l1 ⊔ lsuc l)
  Abstract-Group-Action l =
    Σ (Set l) (λ X → type-hom-Group G (symmetric-Group X))

module _
  {l1 l2 : Level} (G : Group l1) (X : Abstract-Group-Action G l2)
  where

  set-Abstract-Group-Action : Set l2
  set-Abstract-Group-Action = pr1 X

  type-Abstract-Group-Action : UU l2
  type-Abstract-Group-Action = type-Set set-Abstract-Group-Action

  is-set-type-Abstract-Group-Action : is-set type-Abstract-Group-Action
  is-set-type-Abstract-Group-Action = is-set-type-Set set-Abstract-Group-Action
  
  equiv-mul-Abstract-Group-Action :
    type-Group G → type-Abstract-Group-Action ≃ type-Abstract-Group-Action
  equiv-mul-Abstract-Group-Action =
    map-hom-Group G (symmetric-Group set-Abstract-Group-Action) (pr2 X)

  mul-Abstract-Group-Action :
    type-Group G → type-Abstract-Group-Action → type-Abstract-Group-Action
  mul-Abstract-Group-Action g =
    map-equiv (equiv-mul-Abstract-Group-Action g)

  mul-Abstract-Group-Action' :
    type-Abstract-Group-Action → type-Group G → type-Abstract-Group-Action
  mul-Abstract-Group-Action' x g = mul-Abstract-Group-Action g x

  preserves-unit-mul-Abstract-Group-Action :
    (mul-Abstract-Group-Action (unit-Group G)) ~ id
  preserves-unit-mul-Abstract-Group-Action =
    htpy-eq
      ( ap pr1
        ( preserves-unit-hom-Group G
          ( symmetric-Group set-Abstract-Group-Action)
          ( pr2 X)))

  preserves-mul-Abstract-Group-Action :
    (g : type-Group G) (h : type-Group G) (x : type-Abstract-Group-Action) →
    Id ( mul-Abstract-Group-Action (mul-Group G g h) x)
       ( mul-Abstract-Group-Action g (mul-Abstract-Group-Action h x))
  preserves-mul-Abstract-Group-Action g h =
    htpy-eq
      ( ap pr1
        ( preserves-mul-hom-Group G
          ( symmetric-Group set-Abstract-Group-Action) (pr2 X) g h))

  transpose-eq-mul-Abstract-Group-Action :
    (g : type-Group G) (x y : type-Abstract-Group-Action) →
    Id (mul-Abstract-Group-Action g x) y →
    Id x (mul-Abstract-Group-Action (inv-Group G g) y)
  transpose-eq-mul-Abstract-Group-Action g x
    .(mul-Abstract-Group-Action g x) refl =
    ( inv
      ( ( ap (mul-Abstract-Group-Action' x) (left-inverse-law-mul-Group G g)) ∙
        ( preserves-unit-mul-Abstract-Group-Action x))) ∙
    ( preserves-mul-Abstract-Group-Action (inv-Group G g) g x)
```
