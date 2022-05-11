# Loop spaces

```agda
{-# OPTIONS --without-K --exact-split #-}

module synthetic-homotopy-theory.loop-spaces where

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using
  ( id-equiv; _≃_; map-equiv; is-equiv; is-equiv-map-equiv)
open import foundation.identity-types using
  ( Id; refl; _∙_; inv; assoc; left-unit; right-unit; left-inv; right-inv;
    is-binary-equiv-concat)
open import foundation.universe-levels using (Level; UU)

open import structured-types.magmas
open import structured-types.pointed-equivalences using
  ( _≃*_; equiv-pointed-equiv)
open import structured-types.pointed-types using
  ( Pointed-Type; pt-Pointed-Type; type-Pointed-Type)
open import structured-types.wild-unital-magmas
open import structured-types.wild-quasigroups
```

## Idea

The loop space of a pointed type `A` is the pointed type of self-identifications of the base point of `A`. The loop space comes equipped with a groupoidal structure.

## Definitions

### The loop space of a pointed type

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
```

### The magma of loops on a pointed space

```agda
module _
  {l : Level} (A : Pointed-Type l)
  where

  mul-Ω : type-Ω A → type-Ω A → type-Ω A
  mul-Ω x y = x ∙ y

  Ω-Magma : Magma l
  pr1 Ω-Magma = type-Ω A
  pr2 Ω-Magma = mul-Ω
```

### The wild unital magma of loops on a pointed space

```agda
module _
  {l : Level} (A : Pointed-Type l)
  where

  left-unit-law-mul-Ω :
    (x : type-Ω A) → Id (mul-Ω A (refl-Ω A) x) x
  left-unit-law-mul-Ω x = left-unit

  right-unit-law-mul-Ω :
    (x : type-Ω A) → Id (mul-Ω A x (refl-Ω A)) x
  right-unit-law-mul-Ω x = right-unit

  Ω-Wild-Unital-Magma : Wild-Unital-Magma l
  pr1 Ω-Wild-Unital-Magma = Ω A
  pr1 (pr2 Ω-Wild-Unital-Magma) = mul-Ω A
  pr1 (pr2 (pr2 Ω-Wild-Unital-Magma)) = left-unit-law-mul-Ω
  pr1 (pr2 (pr2 (pr2 Ω-Wild-Unital-Magma))) = right-unit-law-mul-Ω
  pr2 (pr2 (pr2 (pr2 Ω-Wild-Unital-Magma))) = refl
```

### The wild quasigroup of loops on a pointed space

```agda
module _
  {l : Level} (A : Pointed-Type l)
  where

  inv-Ω : type-Ω A → type-Ω A
  inv-Ω = inv

  left-inverse-law-mul-Ω :
    (x : type-Ω A) → Id (mul-Ω A (inv-Ω x) x) (refl-Ω A)
  left-inverse-law-mul-Ω x = left-inv x

  right-inverse-law-mul-Ω :
    (x : type-Ω A) → Id (mul-Ω A x (inv-Ω x)) (refl-Ω A)
  right-inverse-law-mul-Ω x = right-inv x

  Ω-Wild-Quasigroup : Wild-Quasigroup l
  pr1 Ω-Wild-Quasigroup = Ω-Magma A
  pr2 Ω-Wild-Quasigroup = is-binary-equiv-concat
```

### Associativity of concatenation on loop spaces

```agda
module _
  {l : Level} (A : Pointed-Type l)
  where
  
  associative-mul-Ω :
    (x y z : type-Ω A) → Id (mul-Ω A (mul-Ω A x y) z) (mul-Ω A x (mul-Ω A y z))
  associative-mul-Ω x y z = assoc x y z
```

-- We compute transport of type-Ω

```
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
