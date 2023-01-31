# Vectors on rings

```agda
{-# OPTIONS --without-K --exact-split #-}

module linear-algebra.vectors-on-rings where

open import elementary-number-theory.natural-numbers

open import foundation.coproduct-types
open import foundation.identity-types
open import foundation.unit-type
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import linear-algebra.constant-vectors using (constant-vec)
open import linear-algebra.functoriality-vectors using
  ( map-binary-vec; htpy-vec; map-vec)
open import linear-algebra.scalar-multiplication-vectors using (scalar-mul-vec)
open import linear-algebra.vectors using
  ( vec; empty-vec; _∷_; head-vec; tail-vec; vec-Set)

open import ring-theory.rings using
  ( Ring; type-Ring; set-Ring; add-Ring; zero-Ring; left-unit-law-add-Ring;
    right-unit-law-add-Ring; neg-Ring; associative-add-Ring;
    left-inverse-law-add-Ring; right-inverse-law-add-Ring; mul-Ring;
    associative-mul-Ring; one-Ring; left-unit-law-mul-Ring;
    commutative-add-Ring;
    left-distributive-mul-add-Ring; right-distributive-mul-add-Ring)

open import univalent-combinatorics.standard-finite-types
```

## Idea

Given a ring `R`, the type `vec n R` of `R`-vectors is an `R`-module

## Definitions

```agda
module _
  {l : Level} (R : Ring l)
  where
  
  vec-Ring : ℕ → UU l
  vec-Ring = vec (type-Ring R)

  head-vec-Ring : {n : ℕ} → vec-Ring (succ-ℕ n) → type-Ring R
  head-vec-Ring v = head-vec v

  tail-vec-Ring : {n : ℕ} → vec-Ring (succ-ℕ n) → vec-Ring n
  tail-vec-Ring v = tail-vec v
```

### Zero vector on a ring

```agda
module _
  {l : Level} (R : Ring l)
  where

  zero-vec-Ring : {n : ℕ} → vec-Ring R n
  zero-vec-Ring {n} = constant-vec (zero-Ring R)
```

### Pointwise addition of vectors on a ring

```agda
module _
  {l : Level} (R : Ring l)
  where

  open import group-theory.semigroups using (Semigroup)
  open import group-theory.monoids using (Monoid)
  open import group-theory.commutative-monoids using (Commutative-Monoid)

  add-vec-Ring : {n : ℕ} → vec-Ring R n → vec-Ring R n → vec-Ring R n
  add-vec-Ring = map-binary-vec (add-Ring R)

  associative-add-vec-Ring :
    {n : ℕ} (v1 v2 v3 : vec-Ring R n) →
    Id ( add-vec-Ring (add-vec-Ring v1 v2) v3)
       ( add-vec-Ring v1 (add-vec-Ring v2 v3))
  associative-add-vec-Ring empty-vec empty-vec empty-vec = refl
  associative-add-vec-Ring (x ∷ v1) (y ∷ v2) (z ∷ v3) =
    ap-binary _∷_
      ( associative-add-Ring R x y z)
      ( associative-add-vec-Ring v1 v2 v3)

  vec-Ring-Semigroup : ℕ → Semigroup l
  vec-Ring-Semigroup n = vec-Set (set-Ring R) n , add-vec-Ring , associative-add-vec-Ring

  left-unit-law-add-vec-Ring :
    {n : ℕ} (v : vec-Ring R n) → Id (add-vec-Ring (zero-vec-Ring R) v) v
  left-unit-law-add-vec-Ring empty-vec = refl
  left-unit-law-add-vec-Ring (x ∷ v) =
    ap-binary _∷_
      ( left-unit-law-add-Ring R x)
      ( left-unit-law-add-vec-Ring v)

  right-unit-law-add-vec-Ring :
    {n : ℕ} (v : vec-Ring R n) → Id (add-vec-Ring v (zero-vec-Ring R)) v
  right-unit-law-add-vec-Ring empty-vec = refl
  right-unit-law-add-vec-Ring (x ∷ v) =
    ap-binary _∷_
      ( right-unit-law-add-Ring R x)
      ( right-unit-law-add-vec-Ring v)

  vec-Ring-Monoid : ℕ → Monoid l
  vec-Ring-Monoid n = vec-Ring-Semigroup n , zero-vec-Ring R , left-unit-law-add-vec-Ring , right-unit-law-add-vec-Ring

  commutative-add-vec-Ring :
    {n : ℕ} (v w : vec-Ring R n) → Id (add-vec-Ring v w) (add-vec-Ring w v)
  commutative-add-vec-Ring empty-vec empty-vec = refl
  commutative-add-vec-Ring (x ∷ v) (y ∷ w) =
    ap-binary _∷_
      ( commutative-add-Ring R x y)
      ( commutative-add-vec-Ring v w)

  vec-Ring-Commutative-Monoid : ℕ → Commutative-Monoid l
  vec-Ring-Commutative-Monoid n = vec-Ring-Monoid n , commutative-add-vec-Ring
```

### The negative of a vector on a ring

```agda
module _
  {l : Level} (R : Ring l)
  where

  open import group-theory.groups
  open import group-theory.abelian-groups using (Ab)

  neg-vec-Ring : {n : ℕ} → vec-Ring R n → vec-Ring R n
  neg-vec-Ring = map-vec (neg-Ring R)

  left-inverse-law-add-vec-Ring :
    {n : ℕ} (v : vec-Ring R n) →
    Id (add-vec-Ring R (neg-vec-Ring v) v) (zero-vec-Ring R)
  left-inverse-law-add-vec-Ring empty-vec = refl
  left-inverse-law-add-vec-Ring (x ∷ v) =
    ap-binary _∷_
      ( left-inverse-law-add-Ring R x)
      ( left-inverse-law-add-vec-Ring v)

  right-inverse-law-add-vec-Ring :
    {n : ℕ} (v : vec-Ring R n) →
    Id (add-vec-Ring R v (neg-vec-Ring v)) (zero-vec-Ring R)
  right-inverse-law-add-vec-Ring empty-vec = refl
  right-inverse-law-add-vec-Ring (x ∷ v) =
    ap-binary _∷_
      ( right-inverse-law-add-Ring R x)
      ( right-inverse-law-add-vec-Ring v)

  vec-Ring-Group : ℕ → Group l
  vec-Ring-Group n = vec-Ring-Semigroup R n ,
    (zero-vec-Ring R , left-unit-law-add-vec-Ring R , right-unit-law-add-vec-Ring R) ,
    (neg-vec-Ring , left-inverse-law-add-vec-Ring , right-inverse-law-add-vec-Ring)

  vec-Ring-Ab : ℕ → Ab l
  vec-Ring-Ab n = vec-Ring-Group n , commutative-add-vec-Ring R
```

### Scalar multiplication of vectors on rings

```agda
module _
  {l : Level} (R : Ring l)
  where

  open import group-theory.abelian-groups using (Ab)
  open import group-theory.homomorphisms-abelian-groups using (type-hom-Ab; map-hom-Ab; eq-htpy-hom-Ab)
  open import group-theory.endomorphism-rings-abelian-groups using (endomorphism-ring-Ab)
  open import ring-theory.homomorphisms-rings using (type-hom-Ring)
  open import ring-theory.modules-rings using (left-module-Ring)

  scalar-mul-vec-Ring : {n : ℕ} (r : type-Ring R) → vec-Ring R n → vec-Ring R n
  scalar-mul-vec-Ring r empty-vec = empty-vec
  scalar-mul-vec-Ring r (x ∷ v) = mul-Ring R r x ∷ scalar-mul-vec-Ring r v

  associative-scalar-mul-vec-Ring :
    {n : ℕ} (r s : type-Ring R) (v : vec-Ring R n) →
    Id ( scalar-mul-vec-Ring (mul-Ring R r s) v)
       ( scalar-mul-vec-Ring r (scalar-mul-vec-Ring s v))
  associative-scalar-mul-vec-Ring r s empty-vec = refl
  associative-scalar-mul-vec-Ring r s (x ∷ v) =
    ap-binary _∷_
      ( associative-mul-Ring R r s x)
      ( associative-scalar-mul-vec-Ring r s v)

  unit-law-scalar-mul-vec-Ring :
    {n : ℕ} (v : vec-Ring R n) → Id (scalar-mul-vec-Ring (one-Ring R) v) v
  unit-law-scalar-mul-vec-Ring empty-vec = refl
  unit-law-scalar-mul-vec-Ring (x ∷ v) =
    ap-binary _∷_ (left-unit-law-mul-Ring R x) (unit-law-scalar-mul-vec-Ring v)

  left-distributive-scalar-mul-add-vec-Ring :
    {n : ℕ} (r : type-Ring R) (v1 v2 : vec-Ring R n) →
    Id ( scalar-mul-vec-Ring r (add-vec-Ring R v1 v2))
       ( add-vec-Ring R (scalar-mul-vec-Ring r v1) (scalar-mul-vec-Ring r v2))
  left-distributive-scalar-mul-add-vec-Ring r empty-vec empty-vec = refl
  left-distributive-scalar-mul-add-vec-Ring r (x ∷ v1) (y ∷ v2) =
    ap-binary _∷_
      ( left-distributive-mul-add-Ring R r x y)
      ( left-distributive-scalar-mul-add-vec-Ring r v1 v2)

  right-distributive-scalar-mul-add-vec-Ring :
    {n : ℕ} (r s : type-Ring R) (v : vec-Ring R n) →
    Id ( scalar-mul-vec-Ring (add-Ring R r s) v)
       ( add-vec-Ring R (scalar-mul-vec-Ring r v) (scalar-mul-vec-Ring s v))
  right-distributive-scalar-mul-add-vec-Ring r s empty-vec = refl
  right-distributive-scalar-mul-add-vec-Ring r s (x ∷ v) =
    ap-binary _∷_
      ( right-distributive-mul-add-Ring R r s x)
      ( right-distributive-scalar-mul-add-vec-Ring r s v)
```

Scalar multiplication defines an `Ab`-endomorphism of `vec-Ring`s, and this mapping is a ring homomorphism `R → End(vec R n)`

```agda
  scalar-mul-vec-Ring-endomorphism : (n : ℕ) (r : type-Ring R) → type-hom-Ab (vec-Ring-Ab R n) (vec-Ring-Ab R n)
  scalar-mul-vec-Ring-endomorphism n r = 
    scalar-mul-vec-Ring r ,
    left-distributive-scalar-mul-add-vec-Ring r

  scalar-mul-hom-Ring : (n : ℕ) → type-hom-Ring R (endomorphism-ring-Ab (vec-Ring-Ab R n))
  scalar-mul-hom-Ring n = (scalar-mul-vec-Ring-endomorphism n , 
    (λ k1 k2 → hom-extensional (right-distributive-scalar-mul-add-vec-Ring k1 k2))), 
    (λ k1 k2 → hom-extensional (associative-scalar-mul-vec-Ring k1 k2)) ,
    hom-extensional (unit-law-scalar-mul-vec-Ring)
      where
        V = vec-Ring-Ab R n
        hom-extensional : {f g : type-hom-Ab V V}
            → ((v : vec-Ring R n) → Id (map-hom-Ab V V f v) (map-hom-Ab V V g v))
            → Id f g
        hom-extensional = eq-htpy-hom-Ab V V

  vec-left-module-Ring : (n : ℕ) → left-module-Ring l R
  vec-left-module-Ring n = vec-Ring-Ab R n , scalar-mul-hom-Ring n
```

## Properties

## Operations on vectors

 - scalar-vector multiplication
 - vector-vector addition
 - scalar/dot/inner product

-- ```agda
-- scalar-product :
--   {l : Level} {A : UU l} {n : ℕ} → (A → A → A) → (A → A → A) → A →
--   vec A n → vec A n → A
-- scalar-product _ _ zeroK empty-vec empty-vec = zeroK
-- scalar-product addK mulK zeroK (x ∷ xs) (y ∷ ys) = addK (mulK x y)
--   (scalar-product addK mulK zeroK xs ys)
-- ```
