# Wild monoids

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

open import wild-algebra.wild-unital-magmas using
  ( Wild-Unital-Magma; type-Wild-Unital-Magma; mul-Wild-Unital-Magma;
    unit-Wild-Unital-Magma; left-unit-law-mul-Wild-Unital-Magma;
    mul-Wild-Unital-Magma'; right-unit-law-mul-Wild-Unital-Magma;
    pointed-type-Wild-Unital-Magma; unital-mul; unital-mul-Wild-Unital-Magma;
    ap-mul-Wild-Unital-Magma; coh-unit-laws-mul-Wild-Unital-Magma;
    hom-Wild-Unital-Magma; preserves-unital-mul; preserves-left-unit-law-mul;
    preserves-right-unit-law-mul; preserves-coh-unit-laws-mul)
```

```agda
unital-associator :
  {l : Level} (M : Wild-Unital-Magma l) → UU l
unital-associator M =
  Σ ( (x y z : type-Wild-Unital-Magma M) →
      Id ( mul-Wild-Unital-Magma M (mul-Wild-Unital-Magma M x y) z)
         ( mul-Wild-Unital-Magma M x (mul-Wild-Unital-Magma M y z)))
    ( λ α111 →
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
                ( λ α110 → unit))))

Wild-Monoid : (l : Level) → UU (lsuc l)
Wild-Monoid l =
  Σ (Wild-Unital-Magma l) unital-associator

wild-unital-magma-Wild-Monoid :
  {l : Level} → Wild-Monoid l → Wild-Unital-Magma l
wild-unital-magma-Wild-Monoid M = pr1 M
      
type-Wild-Monoid :
  {l : Level} → Wild-Monoid l → UU l
type-Wild-Monoid M = type-Wild-Unital-Magma (wild-unital-magma-Wild-Monoid M)

unit-Wild-Monoid :
  {l : Level} (M : Wild-Monoid l) → type-Wild-Monoid M
unit-Wild-Monoid M = unit-Wild-Unital-Magma (wild-unital-magma-Wild-Monoid M)

pointed-type-Wild-Monoid :
  {l : Level} → Wild-Monoid l → Pointed-Type l
pointed-type-Wild-Monoid M =
  pointed-type-Wild-Unital-Magma (wild-unital-magma-Wild-Monoid M)

unital-mul-Wild-Monoid :
  {l : Level} (M : Wild-Monoid l) → unital-mul (pointed-type-Wild-Monoid M)
unital-mul-Wild-Monoid M =
  unital-mul-Wild-Unital-Magma (wild-unital-magma-Wild-Monoid M)

mul-Wild-Monoid :
  {l : Level} (M : Wild-Monoid l) →
  type-Wild-Monoid M → type-Wild-Monoid M → type-Wild-Monoid M
mul-Wild-Monoid M = mul-Wild-Unital-Magma (wild-unital-magma-Wild-Monoid M)

mul-Wild-Monoid' :
  {l : Level} (M : Wild-Monoid l) →
  type-Wild-Monoid M → type-Wild-Monoid M → type-Wild-Monoid M
mul-Wild-Monoid' M = mul-Wild-Unital-Magma' (wild-unital-magma-Wild-Monoid M)

ap-mul-Wild-Monoid :
  {l : Level} (M : Wild-Monoid l) {a b c d : type-Wild-Monoid M} →
  Id a b → Id c d → Id (mul-Wild-Monoid M a c) (mul-Wild-Monoid M b d)
ap-mul-Wild-Monoid M =
  ap-mul-Wild-Unital-Magma (wild-unital-magma-Wild-Monoid M)

left-unit-law-mul-Wild-Monoid :
  {l : Level} (M : Wild-Monoid l) (x : type-Wild-Monoid M) →
  Id (mul-Wild-Monoid M (unit-Wild-Monoid M) x) x
left-unit-law-mul-Wild-Monoid M =
  left-unit-law-mul-Wild-Unital-Magma (wild-unital-magma-Wild-Monoid M)

right-unit-law-mul-Wild-Monoid :
  {l : Level} (M : Wild-Monoid l) (x : type-Wild-Monoid M) →
  Id (mul-Wild-Monoid M x (unit-Wild-Monoid M)) x
right-unit-law-mul-Wild-Monoid M =
  right-unit-law-mul-Wild-Unital-Magma (wild-unital-magma-Wild-Monoid M)

coh-unit-laws-mul-Wild-Monoid :
  {l : Level} (M : Wild-Monoid l) →
  Id (left-unit-law-mul-Wild-Monoid M (unit-Wild-Monoid M))
     (right-unit-law-mul-Wild-Monoid M (unit-Wild-Monoid M))
coh-unit-laws-mul-Wild-Monoid M =
  coh-unit-laws-mul-Wild-Unital-Magma (wild-unital-magma-Wild-Monoid M)

unital-associator-Wild-Monoid :
  {l : Level} (M : Wild-Monoid l) →
  unital-associator (wild-unital-magma-Wild-Monoid M)
unital-associator-Wild-Monoid M = pr2 M

associative-mul-Wild-Monoid :
  {l : Level} (M : Wild-Monoid l) (x y z : type-Wild-Monoid M) →
  Id ( mul-Wild-Monoid M (mul-Wild-Monoid M x y) z)
     ( mul-Wild-Monoid M x (mul-Wild-Monoid M y z))
associative-mul-Wild-Monoid M = pr1 (unital-associator-Wild-Monoid M)

unit-law-110-assoc-Wild-Monoid :
  {l : Level} (M : Wild-Monoid l)
  (x y : type-Wild-Monoid M) →
  Id ( ( associative-mul-Wild-Monoid M x y (unit-Wild-Monoid M)) ∙
       ( ap
         ( mul-Wild-Monoid M x)
         ( right-unit-law-mul-Wild-Monoid M y)))
     ( right-unit-law-mul-Wild-Monoid M
       ( mul-Wild-Monoid M x y))
unit-law-110-assoc-Wild-Monoid M = pr1 (pr2 (pr2 (pr2 (pr2 M))))

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
