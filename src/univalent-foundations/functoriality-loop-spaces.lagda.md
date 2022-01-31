# Functoriality of the loop space operation

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-foundations.functoriality-loop-spaces where

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.identity-types using
  ( Id; refl; ap; ap-concat; _∙_; ap-inv)
open import foundation.universe-levels using (Level; UU)
open import univalent-foundations.loop-spaces using
  ( type-Ω; tr-type-Ω; preserves-refl-tr-Ω; Ω; mul-Ω; preserves-mul-tr-Ω; inv-Ω;
    preserves-inv-tr-Ω)
open import univalent-foundations.pointed-maps using
  ( _→*_; preserves-point-map-pointed-map; map-pointed-map)
open import univalent-foundations.pointed-types using
  ( Pointed-Type)
```

## Idea

Any pointed map `f : A →* B` induces a map `map-Ω f : Ω A →* Ω B`. Furthermore, this operation respects the groupoidal operations on loop spaces.

## Definition

```agda
module _
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2) (f : A →* B)
  where

  map-Ω : type-Ω A → type-Ω B
  map-Ω p =
    tr-type-Ω
      ( preserves-point-map-pointed-map A B f)
      ( ap (map-pointed-map A B f) p)
  
  preserves-refl-map-Ω : Id (map-Ω refl) refl
  preserves-refl-map-Ω = preserves-refl-tr-Ω (pr2 f)

  pointed-map-Ω : Ω A →* Ω B
  pointed-map-Ω = pair map-Ω preserves-refl-map-Ω

  preserves-mul-map-Ω :
    (x y : type-Ω A) → Id (map-Ω (mul-Ω A x y)) (mul-Ω B (map-Ω x) (map-Ω y))
  preserves-mul-map-Ω x y =
    ( ap
      ( tr-type-Ω (preserves-point-map-pointed-map A B f))
      ( ap-concat (map-pointed-map A B f) x y)) ∙
    ( preserves-mul-tr-Ω
      ( preserves-point-map-pointed-map A B f)
      ( ap (map-pointed-map A B f) x)
      ( ap (map-pointed-map A B f) y))

  preserves-inv-map-Ω :
    (x : type-Ω A) → Id (map-Ω (inv-Ω A x)) (inv-Ω B (map-Ω x))
  preserves-inv-map-Ω x =
    ( ap
      ( tr-type-Ω (preserves-point-map-pointed-map A B f))
      ( ap-inv (map-pointed-map A B f) x)) ∙
    ( preserves-inv-tr-Ω
      ( preserves-point-map-pointed-map A B f)
      ( ap (map-pointed-map A B f) x))
```
