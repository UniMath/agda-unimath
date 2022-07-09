---
title: Conjugation in groups
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module group-theory.conjugation where

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using
  ( _≃_; _∘e_; map-equiv; eq-htpy-equiv)
open import foundation.identity-types using (_∙_; inv; ap)
open import foundation.universe-levels using (Level)

open import group-theory.group-actions using
  ( Abstract-Group-Action)
open import group-theory.groups using
  ( Group; type-Group; equiv-mul-Group'; inv-Group; equiv-mul-Group; set-Group;
    ap-mul-Group; associative-mul-Group; distributive-inv-mul-Group; mul-Group;
    mul-Group')
```

## Idea

Conjugation by an element `x` in a group `G` is the map `y ↦ (xy)x⁻¹`.

## Definition

### Conjugation

```agda
module _
  {l : Level} (G : Group l)
  where

  equiv-conjugation-Group : (x : type-Group G) → type-Group G ≃ type-Group G
  equiv-conjugation-Group x =
    equiv-mul-Group' G (inv-Group G x) ∘e equiv-mul-Group G x

  conjugation-Group : (x : type-Group G) → type-Group G → type-Group G
  conjugation-Group x = map-equiv (equiv-conjugation-Group x)
```

### The conjugation action of a group on itself

```agda
module _
  {l1 : Level} (G : Group l1)
  where

  conjugation-Abstract-Group-Action : Abstract-Group-Action G l1
  pr1 conjugation-Abstract-Group-Action = set-Group G
  pr1 (pr2 conjugation-Abstract-Group-Action) g = equiv-conjugation-Group G g
  pr2 (pr2 conjugation-Abstract-Group-Action) g h =
    eq-htpy-equiv
      ( λ x →
        ( ap-mul-Group G
          ( associative-mul-Group G g h x)
          ( distributive-inv-mul-Group G g h)) ∙
        ( ( inv
            ( associative-mul-Group G
              ( mul-Group G g (mul-Group G h x))
              ( inv-Group G h)
              ( inv-Group G g))) ∙
          ( ap
            ( mul-Group' G (inv-Group G g))
            ( associative-mul-Group G g
              ( mul-Group G h x)
              ( inv-Group G h)))))
```
