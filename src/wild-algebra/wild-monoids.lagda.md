---
title: Wild monoids
---

```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module wild-algebra.wild-monoids where

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.identity-types using (Id; _∙_; ap)
open import foundation.unit-type using (unit; star)
open import foundation.universe-levels using (Level; UU; lsuc; _⊔_)

open import group-theory.homomorphisms-semigroups using (preserves-mul)

open import synthetic-homotopy-theory.pointed-maps using (_→*_)
open import synthetic-homotopy-theory.pointed-types using
  ( Pointed-Type)

open import wild-algebra.morphisms-wild-unital-magmas using
  ( hom-Wild-Unital-Magma; preserves-unital-mul; preserves-left-unit-law-mul;
    preserves-right-unit-law-mul; preserves-coh-unit-laws-mul)
open import wild-algebra.wild-unital-magmas using
  ( Wild-Unital-Magma; type-Wild-Unital-Magma; mul-Wild-Unital-Magma;
    unit-Wild-Unital-Magma; left-unit-law-mul-Wild-Unital-Magma;
    mul-Wild-Unital-Magma'; right-unit-law-mul-Wild-Unital-Magma;
    pointed-type-Wild-Unital-Magma; unital-mul-Pointed-Type;
    unital-mul-Wild-Unital-Magma; ap-mul-Wild-Unital-Magma;
    coh-unit-laws-mul-Wild-Unital-Magma)
```

## Idea

## Definition

### Unital associators on wild unital magmas

```agda
module _
  {l : Level} (M : Wild-Unital-Magma l)
  where
  
  associator-Wild-Unital-Magma : UU l
  associator-Wild-Unital-Magma =
    (x y z : type-Wild-Unital-Magma M) →
    Id ( mul-Wild-Unital-Magma M (mul-Wild-Unital-Magma M x y) z)
      ( mul-Wild-Unital-Magma M x (mul-Wild-Unital-Magma M y z))
     
  is-unital-associator : (α : associator-Wild-Unital-Magma) → UU l
  is-unital-associator α111 =
    Σ ( (y z : type-Wild-Unital-Magma M) →
        Id ( ( α111 (unit-Wild-Unital-Magma M) y z) ∙
             ( left-unit-law-mul-Wild-Unital-Magma M
           ( mul-Wild-Unital-Magma M y z)))
             ( ap
               ( mul-Wild-Unital-Magma' M z)
               ( left-unit-law-mul-Wild-Unital-Magma M y)))
      ( λ α011 →
        Σ ( (x z : type-Wild-Unital-Magma M) →
            Id ( ( α111 x (unit-Wild-Unital-Magma M) z) ∙
                 ( ap
                   ( mul-Wild-Unital-Magma M x)
                   ( left-unit-law-mul-Wild-Unital-Magma M z)))
               ( ap
                 ( mul-Wild-Unital-Magma' M z)
                 ( right-unit-law-mul-Wild-Unital-Magma M x)))
          ( λ α101 →
            Σ ( (x y : type-Wild-Unital-Magma M) →
                Id ( ( α111 x y (unit-Wild-Unital-Magma M)) ∙
                     ( ap
                       ( mul-Wild-Unital-Magma M x)
                       ( right-unit-law-mul-Wild-Unital-Magma M y)))
                   ( right-unit-law-mul-Wild-Unital-Magma M
                     ( mul-Wild-Unital-Magma M x y)))
              ( λ α110 → unit)))

  unital-associator : UU l
  unital-associator = Σ ( associator-Wild-Unital-Magma) is-unital-associator
```

### Wild monoids

```agda
Wild-Monoid : (l : Level) → UU (lsuc l)
Wild-Monoid l =
  Σ (Wild-Unital-Magma l) unital-associator

module _
  {l : Level} (M : Wild-Monoid l)
  where

  wild-unital-magma-Wild-Monoid : Wild-Unital-Magma l
  wild-unital-magma-Wild-Monoid = pr1 M
      
  type-Wild-Monoid : UU l
  type-Wild-Monoid = type-Wild-Unital-Magma wild-unital-magma-Wild-Monoid

  unit-Wild-Monoid : type-Wild-Monoid
  unit-Wild-Monoid = unit-Wild-Unital-Magma wild-unital-magma-Wild-Monoid

  pointed-type-Wild-Monoid : Pointed-Type l
  pointed-type-Wild-Monoid =
    pointed-type-Wild-Unital-Magma wild-unital-magma-Wild-Monoid

  unital-mul-Wild-Monoid : unital-mul-Pointed-Type pointed-type-Wild-Monoid
  unital-mul-Wild-Monoid =
    unital-mul-Wild-Unital-Magma wild-unital-magma-Wild-Monoid

  mul-Wild-Monoid : type-Wild-Monoid → type-Wild-Monoid → type-Wild-Monoid
  mul-Wild-Monoid = mul-Wild-Unital-Magma wild-unital-magma-Wild-Monoid

  mul-Wild-Monoid' : type-Wild-Monoid → type-Wild-Monoid → type-Wild-Monoid
  mul-Wild-Monoid' = mul-Wild-Unital-Magma' wild-unital-magma-Wild-Monoid

  ap-mul-Wild-Monoid :
    {a b c d : type-Wild-Monoid} →
    Id a b → Id c d → Id (mul-Wild-Monoid a c) (mul-Wild-Monoid b d)
  ap-mul-Wild-Monoid = ap-mul-Wild-Unital-Magma wild-unital-magma-Wild-Monoid

  left-unit-law-mul-Wild-Monoid :
    (x : type-Wild-Monoid) → Id (mul-Wild-Monoid unit-Wild-Monoid x) x
  left-unit-law-mul-Wild-Monoid =
    left-unit-law-mul-Wild-Unital-Magma wild-unital-magma-Wild-Monoid

  right-unit-law-mul-Wild-Monoid :
    (x : type-Wild-Monoid ) → Id (mul-Wild-Monoid x unit-Wild-Monoid) x
  right-unit-law-mul-Wild-Monoid =
    right-unit-law-mul-Wild-Unital-Magma wild-unital-magma-Wild-Monoid

  coh-unit-laws-mul-Wild-Monoid :
    Id ( left-unit-law-mul-Wild-Monoid unit-Wild-Monoid)
       ( right-unit-law-mul-Wild-Monoid unit-Wild-Monoid)
  coh-unit-laws-mul-Wild-Monoid =
    coh-unit-laws-mul-Wild-Unital-Magma wild-unital-magma-Wild-Monoid

  unital-associator-Wild-Monoid :
    unital-associator wild-unital-magma-Wild-Monoid
  unital-associator-Wild-Monoid = pr2 M

  associative-mul-Wild-Monoid :
    (x y z : type-Wild-Monoid) →
    Id ( mul-Wild-Monoid (mul-Wild-Monoid x y) z)
       ( mul-Wild-Monoid x (mul-Wild-Monoid y z))
  associative-mul-Wild-Monoid = pr1 unital-associator-Wild-Monoid

  unit-law-110-assoc-Wild-Monoid :
    (x y : type-Wild-Monoid) →
    Id ( ( associative-mul-Wild-Monoid x y unit-Wild-Monoid) ∙
         ( ap (mul-Wild-Monoid x) (right-unit-law-mul-Wild-Monoid y)))
       ( right-unit-law-mul-Wild-Monoid (mul-Wild-Monoid x y))
  unit-law-110-assoc-Wild-Monoid = pr1 (pr2 (pr2 (pr2 (pr2 M))))

-- In the definition of morphisms of wild monoids we only require the unit and
-- multiplication to be preserved. This is because we would need further
-- coherence in wild monoids if we want morphisms list X → M to preserve the
-- unital associator.

module _
  {l1 l2 : Level} (M : Wild-Monoid l1) (N : Wild-Monoid l2)
  where
  
  hom-Wild-Monoid : UU (l1 ⊔ l2)
  hom-Wild-Monoid =
    hom-Wild-Unital-Magma
      ( wild-unital-magma-Wild-Monoid M)
      ( wild-unital-magma-Wild-Monoid N)

  pointed-map-hom-Wild-Monoid :
    hom-Wild-Monoid → pointed-type-Wild-Monoid M →* pointed-type-Wild-Monoid N
  pointed-map-hom-Wild-Monoid f = pr1 f

  map-hom-Wild-Monoid :
    hom-Wild-Monoid → type-Wild-Monoid M → type-Wild-Monoid N
  map-hom-Wild-Monoid f = pr1 (pr1 f)

  preserves-unit-map-hom-Wild-Monoid :
    (f : hom-Wild-Monoid) →
    Id (map-hom-Wild-Monoid f (unit-Wild-Monoid M)) (unit-Wild-Monoid N)
  preserves-unit-map-hom-Wild-Monoid f = pr2 (pr1 f)

  preserves-unital-mul-map-hom-Wild-Monoid :
    (f : hom-Wild-Monoid) →
    preserves-unital-mul
      ( wild-unital-magma-Wild-Monoid M)
      ( wild-unital-magma-Wild-Monoid N)
      ( pointed-map-hom-Wild-Monoid f)
  preserves-unital-mul-map-hom-Wild-Monoid f = pr2 f

  preserves-mul-map-hom-Wild-Monoid :
    (f : hom-Wild-Monoid) →
    preserves-mul
      ( mul-Wild-Monoid M)
      ( mul-Wild-Monoid N)
      ( map-hom-Wild-Monoid f)
  preserves-mul-map-hom-Wild-Monoid f = pr1 (pr2 f)

  preserves-left-unit-law-mul-map-hom-Wild-Monoid :
    ( f : hom-Wild-Monoid) →
    preserves-left-unit-law-mul
      ( mul-Wild-Monoid M)
      ( left-unit-law-mul-Wild-Monoid M)
      ( mul-Wild-Monoid N)
      ( left-unit-law-mul-Wild-Monoid N)
      ( map-hom-Wild-Monoid f)
      ( preserves-unit-map-hom-Wild-Monoid f)
      ( preserves-mul-map-hom-Wild-Monoid f)
  preserves-left-unit-law-mul-map-hom-Wild-Monoid f =
    pr1 (pr2 (pr2 f))

  preserves-right-unit-law-mul-map-hom-Wild-Monoid :
    (f : hom-Wild-Monoid) →
    preserves-right-unit-law-mul
      ( mul-Wild-Monoid M)
      ( right-unit-law-mul-Wild-Monoid M)
      ( mul-Wild-Monoid N)
      ( right-unit-law-mul-Wild-Monoid N)
      ( map-hom-Wild-Monoid f)
      ( preserves-unit-map-hom-Wild-Monoid f)
      ( preserves-mul-map-hom-Wild-Monoid f)
  preserves-right-unit-law-mul-map-hom-Wild-Monoid f =
    pr1 (pr2 (pr2 (pr2 f)))

  preserves-coh-unit-laws-map-hom-Wild-Monoid :
    (f : hom-Wild-Monoid) →
    preserves-coh-unit-laws-mul
      ( wild-unital-magma-Wild-Monoid M)
      ( wild-unital-magma-Wild-Monoid N)
      ( pointed-map-hom-Wild-Monoid f)
      ( preserves-mul-map-hom-Wild-Monoid f)
      ( preserves-left-unit-law-mul-map-hom-Wild-Monoid f)
      ( preserves-right-unit-law-mul-map-hom-Wild-Monoid f)
  preserves-coh-unit-laws-map-hom-Wild-Monoid f =
    pr2 (pr2 (pr2 (pr2 f)))

-- htpy-hom-Wild-Monoid :
--   {l1 l2 : Level} (M : Wild-Monoid l1) (N : Wild-Monoid l2)
--   (f g : hom-Wild-Monoid M N) → UU (l1 ⊔ l2)
-- htpy-hom-Wild-Monoid M N f g =
--   Σ ( Σ ( map-hom-Wild-Monoid M N f ~ map-hom-Wild-Monoid M N g)
--         ( λ H →
--           ( x y : type-Wild-Monoid M) →
--           Id ( ( preserves-mul-map-hom-Wild-Monoid M N f x y) ∙
--                ( ap-mul-Wild-Monoid N (H x) (H y)))
--              ( ( H (mul-Wild-Monoid M x y)) ∙
--                ( preserves-mul-map-hom-Wild-Monoid M N g x y))))
--     ( λ Hμ →
--       Id ( preserves-unit-map-hom-Wild-Monoid M N f)
--          ( pr1 Hμ (unit-Wild-Monoid M) ∙ preserves-unit-map-hom-Wild-Monoid M N g))

-- refl-htpy-hom-Wild-Monoid :
--   {l1 l2 : Level} (M : Wild-Monoid l1) (N : Wild-Monoid l2)
--   (f : hom-Wild-Monoid M N) → htpy-hom-Wild-Monoid M N f f
-- refl-htpy-hom-Wild-Monoid M N f =
--   pair (pair refl-htpy (λ x y → right-unit)) refl

-- {-
-- is-contr-total-htpy-hom-Wild-Monoid :
--   {l1 l2 : Level} (M : Wild-Monoid l1) (N : Wild-Monoid l2)
--   (f : hom-Wild-Monoid M N) →
--   is-contr (Σ (hom-Wild-Monoid M N) (htpy-hom-Wild-Monoid M N f))
-- is-contr-total-htpy-hom-Wild-Monoid M N f =
--   is-contr-total-Eq-structure
--     {! λ fμ p!}
--     {!!}
--     {!!}
--     {!!}
-- -}
