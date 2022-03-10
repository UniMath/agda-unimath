{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module wild-algebra.wild-monoids where

open import wild-algebra.wild-unital-magmas public

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
  {l : Level} → Wild-Monoid l → UU-pt l
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

-- We introduce the wild monoid of lists of elements of X.

unit-law-011-assoc-concat-list :
  {l1 : Level} {X : UU l1} (y z : list X) →
  Id ( ( assoc-concat-list nil y z) ∙
       ( left-unit-law-concat-list (concat-list y z)))
     ( ap (λ t → concat-list t z) (left-unit-law-concat-list y))
unit-law-011-assoc-concat-list y z = refl

concat-list' : {l : Level} {A : UU l} → list A → list A → list A
concat-list' x y = concat-list y x

unit-law-101-assoc-concat-list :
  {l1 : Level} {X : UU l1} (x z : list X) →
  Id ( ( assoc-concat-list x nil z) ∙
       ( ap (concat-list x) (left-unit-law-concat-list z)))
     ( ap (λ t → concat-list t z) (right-unit-law-concat-list x))
unit-law-101-assoc-concat-list nil z = refl
unit-law-101-assoc-concat-list (cons x l) z =
  ( ( ( inv
        ( ap-concat
          ( cons x)
          ( assoc-concat-list l nil z)
          ( ap (concat-list l) (left-unit-law-concat-list z)))) ∙
      ( ap (ap (cons x)) (unit-law-101-assoc-concat-list l z))) ∙
    ( inv (ap-comp (cons x) (concat-list' z) (right-unit-law-concat-list l)))) ∙
  ( ap-comp (concat-list' z) (cons x) (right-unit-law-concat-list l))

unit-law-110-assoc-concat-list :
  {l1 : Level} {X : UU l1} (x y : list X) →
  Id ( ( assoc-concat-list x y nil) ∙
       ( ap (concat-list x) (right-unit-law-concat-list y)))
     ( right-unit-law-concat-list (concat-list x y))
unit-law-110-assoc-concat-list nil y = ap-id (right-unit-law-concat-list y)
unit-law-110-assoc-concat-list (cons a x) y =
  ( ap
    ( concat (assoc-concat-list (cons a x) y nil) (concat-list (cons a x) y))
    ( ap-comp (cons a) (concat-list x) (right-unit-law-concat-list y))) ∙
  ( ( inv
      ( ap-concat
        ( cons a)
        ( assoc-concat-list x y nil)
        ( ap (concat-list x) (right-unit-law-concat-list y)))) ∙
    ( ap (ap (cons a)) (unit-law-110-assoc-concat-list x y)))

list-Wild-Monoid : {l : Level} → UU l → Wild-Monoid l
list-Wild-Monoid X =
  pair
    ( list-Wild-Unital-Magma X)
    ( pair
      ( assoc-concat-list)
      ( pair
        ( unit-law-011-assoc-concat-list)
        ( pair
          ( unit-law-101-assoc-concat-list)
          ( pair unit-law-110-assoc-concat-list star))))

module _
  {l1 l2 : Level} {X : UU l1} (M : Wild-Monoid l2) (f : X → type-Wild-Monoid M)
  where

  map-elim-list-Wild-Monoid :
    list X → type-Wild-Monoid M
  map-elim-list-Wild-Monoid nil = unit-Wild-Monoid M
  map-elim-list-Wild-Monoid (cons u x) =
    mul-Wild-Monoid M (f u) (map-elim-list-Wild-Monoid x)

  preserves-unit-map-elim-list-Wild-Monoid :
    Id (map-elim-list-Wild-Monoid nil) (unit-Wild-Monoid M)
  preserves-unit-map-elim-list-Wild-Monoid = refl

  preserves-mul-map-elim-list-Wild-Monoid :
    preserves-mul
      ( concat-list)
      ( mul-Wild-Monoid M)
      ( map-elim-list-Wild-Monoid)
  preserves-mul-map-elim-list-Wild-Monoid nil y =
    inv (left-unit-law-mul-Wild-Monoid M (map-elim-list-Wild-Monoid y))
  preserves-mul-map-elim-list-Wild-Monoid (cons u x) y =
    ( ap (mul-Wild-Monoid M (f u))
      ( preserves-mul-map-elim-list-Wild-Monoid x y)) ∙
    ( inv
      ( associative-mul-Wild-Monoid M
        ( f u)
        ( map-elim-list-Wild-Monoid x)
        ( map-elim-list-Wild-Monoid y)))

  preserves-left-unit-law-map-elim-list-Wild-Monoid :
    preserves-left-unit-law-mul
      ( concat-list)
      { nil}
      ( left-unit-law-concat-list)
      ( mul-Wild-Monoid M)
      ( left-unit-law-mul-Wild-Monoid M)
      ( map-elim-list-Wild-Monoid)
      ( preserves-unit-map-elim-list-Wild-Monoid)
      ( preserves-mul-map-elim-list-Wild-Monoid)
  preserves-left-unit-law-map-elim-list-Wild-Monoid x =
    inv
      ( left-inv
        ( left-unit-law-mul-Wild-Monoid M (map-elim-list-Wild-Monoid x)))

  preserves-right-unit-law-map-elim-list-Wild-Monoid :
    preserves-right-unit-law-mul
      ( concat-list)
      { nil}
      ( right-unit-law-concat-list)
      ( mul-Wild-Monoid M)
      ( right-unit-law-mul-Wild-Monoid M)
      ( map-elim-list-Wild-Monoid)
      ( preserves-unit-map-elim-list-Wild-Monoid)
      ( preserves-mul-map-elim-list-Wild-Monoid)
  preserves-right-unit-law-map-elim-list-Wild-Monoid nil =
    ( inv (left-inv (left-unit-law-mul-Wild-Monoid M (unit-Wild-Monoid M)))) ∙
    ( ap
      ( concat
        ( inv (left-unit-law-mul-Wild-Monoid M (unit-Wild-Monoid M)))
        ( unit-Wild-Monoid M))
      ( coh-unit-laws-mul-Wild-Monoid M))
  preserves-right-unit-law-map-elim-list-Wild-Monoid (cons a x) =
    ( inv
      ( ap-comp
        ( map-elim-list-Wild-Monoid)
        ( cons a)
        ( right-unit-law-concat-list x))) ∙
    ( ( ap-comp
        ( mul-Wild-Monoid M (f a))
        ( map-elim-list-Wild-Monoid)
        ( right-unit-law-concat-list x)) ∙
      ( ( ap
          ( ap (mul-Wild-Monoid M (f a)))
          ( preserves-right-unit-law-map-elim-list-Wild-Monoid x)) ∙
        ( ( ap-concat
            ( mul-Wild-Monoid M (f a))
            ( preserves-mul-map-elim-list-Wild-Monoid x nil)
            ( right-unit-law-mul-Wild-Monoid M
              ( map-elim-list-Wild-Monoid x))) ∙
          ( ( ap
              ( concat
                ( ap
                  ( mul-Wild-Monoid M (f a))
                  ( preserves-mul-map-elim-list-Wild-Monoid x nil))
                ( map-elim-list-Wild-Monoid (cons a x)))
              ( ( ap
                  ( concat'
                    ( mul-Wild-Monoid M
                      ( f a)
                      ( mul-Wild-Monoid M
                        ( map-elim-list-Wild-Monoid x)
                        ( unit-Wild-Monoid M)))
                    ( ap
                      ( mul-Wild-Monoid M (f a))
                      ( right-unit-law-mul-Wild-Monoid M
                        ( map-elim-list-Wild-Monoid x))))
                  ( inv
                    ( left-inv
                      ( associative-mul-Wild-Monoid M
                        ( f a)
                        ( map-elim-list-Wild-Monoid x)
                        ( unit-Wild-Monoid M))))) ∙
                ( ( assoc
                    ( inv
                      ( associative-mul-Wild-Monoid M
                        ( f a)
                        ( map-elim-list-Wild-Monoid x)
                        ( unit-Wild-Monoid M)))
                    ( associative-mul-Wild-Monoid M
                      ( f a)
                      ( map-elim-list-Wild-Monoid x)
                      ( unit-Wild-Monoid M))
                    ( ap
                      ( mul-Wild-Monoid M (f a))
                      ( right-unit-law-mul-Wild-Monoid M
                        ( map-elim-list-Wild-Monoid x)))) ∙
                  ( ap
                    ( concat
                      ( inv
                        ( associative-mul-Wild-Monoid M
                          ( f a)
                          ( map-elim-list-Wild-Monoid x)
                          ( unit-Wild-Monoid M)))
                      ( map-elim-list-Wild-Monoid (cons a x)))
                    ( unit-law-110-assoc-Wild-Monoid M
                      ( f a)
                      ( map-elim-list-Wild-Monoid x)))))) ∙
            ( inv
              ( assoc
                ( ap
                  ( mul-Wild-Monoid M (f a))
                  ( preserves-mul-map-elim-list-Wild-Monoid x nil))
                ( inv
                  ( associative-mul-Wild-Monoid M
                    ( f a)
                    ( map-elim-list-Wild-Monoid x)
                    ( unit-Wild-Monoid M)))
                ( right-unit-law-mul-Wild-Monoid M
                  ( map-elim-list-Wild-Monoid (cons a x)))))))))

preserves-coh-unit-laws-map-elim-list-Wild-Monoid :
  {l1 l2 : Level} {X : UU l1} (M : Wild-Monoid l2)
  (f : X → type-Wild-Monoid M) → 
  preserves-coh-unit-laws-mul
    ( list-Wild-Unital-Magma X)
    ( wild-unital-magma-Wild-Monoid M)
    ( pair (map-elim-list-Wild-Monoid M f) refl)
    ( preserves-mul-map-elim-list-Wild-Monoid M f)
    ( preserves-left-unit-law-map-elim-list-Wild-Monoid M f)
    ( preserves-right-unit-law-map-elim-list-Wild-Monoid M f)
preserves-coh-unit-laws-map-elim-list-Wild-Monoid
  (pair (pair (pair M eM) (pair μ (pair lM (pair rM cM)))) αM) f = refl
  
elim-list-Wild-Monoid :
  {l1 l2 : Level} {X : UU l1} (M : Wild-Monoid l2)
  (f : X → type-Wild-Monoid M) →
  hom-Wild-Monoid (list-Wild-Monoid X) M
elim-list-Wild-Monoid M f =
  pair
    ( pair (map-elim-list-Wild-Monoid M f) refl)
    ( pair
      ( preserves-mul-map-elim-list-Wild-Monoid M f)
      ( pair (preserves-left-unit-law-map-elim-list-Wild-Monoid M f)
        ( pair
          ( preserves-right-unit-law-map-elim-list-Wild-Monoid M f)
          ( preserves-coh-unit-laws-map-elim-list-Wild-Monoid M f))))

-- htpy-elim-list-Wild-Monoid :
--   {l1 l2 : Level} {X : UU l1} (M : Wild-Monoid l2)
--   (g h : hom-Wild-Monoid (list-Wild-Monoid X) M)
--   ( H : ( map-hom-Wild-Monoid (list-Wild-Monoid X) M g ∘ unit-list) ~
--         ( map-hom-Wild-Monoid (list-Wild-Monoid X) M h ∘ unit-list)) →
--   htpy-hom-Wild-Monoid (list-Wild-Monoid X) M g h
-- htpy-elim-list-Wild-Monoid {X = X} M g h H =
--   pair (pair α β) γ
--   where
--   α : pr1 (pr1 g) ~ pr1 (pr1 h)
--   α nil =
--     ( preserves-unit-map-hom-Wild-Monoid (list-Wild-Monoid X) M g) ∙
--     ( inv (preserves-unit-map-hom-Wild-Monoid (list-Wild-Monoid X) M h))
--   α (cons x l) =
--     ( preserves-mul-map-hom-Wild-Monoid
--       ( list-Wild-Monoid X)
--       ( M)
--       ( g)
--       ( unit-list x)
--       ( l)) ∙
--     ( ( ap-mul-Wild-Monoid M (H x) (α l)) ∙
--       ( inv
--         ( preserves-mul-map-hom-Wild-Monoid
--           ( list-Wild-Monoid X)
--           ( M)
--           ( h)
--           ( unit-list x)
--           ( l))))
--   β : (x y : pr1 (pr1 (list-Wild-Monoid X))) →
--       Id ( pr2 (pr1 g) x y ∙ ap-mul-Wild-Monoid M (α x) (α y))
--          ( α (concat-list x y) ∙ pr2 (pr1 h) x y)
--   β nil y = {!!}
--   β (cons x x₁) y = {!!}
--   γ : Id (pr2 g) (α nil ∙ pr2 h)
--   γ =
--     ( inv right-unit) ∙
--     ( ( ap (concat (pr2 g) (pr1 (pr2 M))) (inv (left-inv (pr2 h)))) ∙
--       ( inv (assoc (pr2 g) (inv (pr2 h)) (pr2 h))))
