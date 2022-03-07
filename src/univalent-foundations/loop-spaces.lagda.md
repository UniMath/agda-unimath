# Loop spaces

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-foundations.loop-spaces where

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using
  ( id-equiv; _≃_; map-equiv; is-equiv; is-equiv-map-equiv)
open import foundation.identity-types using
  ( Id; refl; _∙_; inv; assoc; left-unit; right-unit; left-inv; right-inv)
open import foundation.universe-levels using (Level; UU)

open import synthetic-homotopy-theory.pointed-equivalences using
  ( _≃*_; equiv-pointed-equiv)
open import synthetic-homotopy-theory.pointed-types using
  ( Pointed-Type; pt-Pointed-Type; type-Pointed-Type)
```

## Idea

The loop space of a pointed type `A` is the pointed type of self-identifications of the base point of `A`. The loop space comes equipped with a groupoidal structure.

## Definition

```agda
module _
  {l : Level} (A : Pointed-Type l)
  where
  
  type-Ω : UU l
  type-Ω = Id (pt-Pointed-Type A) (pt-Pointed-Type A)

  refl-Ω : type-Ω
  refl-Ω = refl

  Ω : Pointed-Type l
  Ω = pair type-Ω refl-Ω

  -- Wild group structure on loop spaces

  mul-Ω : type-Ω → type-Ω → type-Ω
  mul-Ω x y = x ∙ y

  inv-Ω : type-Ω → type-Ω
  inv-Ω = inv

  associative-mul-Ω :
    (x y z : type-Ω) → Id (mul-Ω (mul-Ω x y) z) (mul-Ω x (mul-Ω y z))
  associative-mul-Ω x y z = assoc x y z

  left-unit-law-mul-Ω :
    (x : type-Ω) → Id (mul-Ω refl-Ω x) x
  left-unit-law-mul-Ω x = left-unit

  right-unit-law-mul-Ω :
    (x : type-Ω) → Id (mul-Ω x refl-Ω) x
  right-unit-law-mul-Ω x = right-unit

  left-inverse-law-mul-Ω :
    (x : type-Ω) → Id (mul-Ω (inv-Ω x) x) refl-Ω
  left-inverse-law-mul-Ω x = left-inv x

  right-inverse-law-mul-Ω :
    (x : type-Ω) → Id (mul-Ω x (inv-Ω x)) refl-Ω
  right-inverse-law-mul-Ω x = right-inv x

-- We compute transport of type-Ω

module _
  {l1 : Level} {A : UU l1} {x y : A} 
  where

  equiv-tr-Ω : Id x y → Ω (pair A x) ≃* Ω (pair A y)
  equiv-tr-Ω refl = pair id-equiv refl
  
  equiv-tr-type-Ω : Id x y → type-Ω (pair A x) ≃ type-Ω (pair A y)
  equiv-tr-type-Ω p =
    equiv-pointed-equiv (Ω (pair A x)) (Ω (pair A y)) (equiv-tr-Ω p)

  tr-type-Ω : Id x y → type-Ω (pair A x) → type-Ω (pair A y)
  tr-type-Ω p = map-equiv (equiv-tr-type-Ω p)

  is-equiv-tr-type-Ω : (p : Id x y) → is-equiv (tr-type-Ω p)
  is-equiv-tr-type-Ω p = is-equiv-map-equiv (equiv-tr-type-Ω p)

  preserves-refl-tr-Ω : (p : Id x y) → Id (tr-type-Ω p refl) refl
  preserves-refl-tr-Ω refl = refl

  preserves-mul-tr-Ω :
    (p : Id x y) (u v : type-Ω (pair A x)) →
    Id ( tr-type-Ω p (mul-Ω (pair A x) u v))
       ( mul-Ω (pair A y) (tr-type-Ω p u) (tr-type-Ω p v))
  preserves-mul-tr-Ω refl u v = refl

  preserves-inv-tr-Ω :
    (p : Id x y) (u : type-Ω (pair A x)) →
    Id ( tr-type-Ω p (inv-Ω (pair A x) u))
       ( inv-Ω (pair A y) (tr-type-Ω p u))
  preserves-inv-tr-Ω refl u = refl
```
