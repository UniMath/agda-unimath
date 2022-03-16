# Ring homomorphisms

```agda
{-# OPTIONS --without-K --exact-split #-}

module ring-theory.ring-homomorphisms where
```

## Definition

```agda
{- Ring homomorphisms -}

preserves-mul-hom-Ab :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
  hom-Ab (ab-Ring R1) (ab-Ring R2) → UU (l1 ⊔ l2)
preserves-mul-hom-Ab R1 R2 f =
  (x y : type-Ring R1) →
  Id ( map-hom-Ab (ab-Ring R1) (ab-Ring R2) f (mul-Ring R1 x y))
     ( mul-Ring R2
       ( map-hom-Ab (ab-Ring R1) (ab-Ring R2) f x)
       ( map-hom-Ab (ab-Ring R1) (ab-Ring R2) f y))

is-prop-preserves-mul-hom-Ab :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
  ( f : hom-Ab (ab-Ring R1) (ab-Ring R2)) →
  is-prop (preserves-mul-hom-Ab R1 R2 f)
is-prop-preserves-mul-hom-Ab R1 R2 f =
  is-prop-Π
    ( λ x →
      is-prop-Π
        ( λ y →
          is-set-type-Ring R2
            ( map-hom-Ab (ab-Ring R1) (ab-Ring R2) f (mul-Ring R1 x y))
            ( mul-Ring R2
              ( map-hom-Ab (ab-Ring R1) (ab-Ring R2) f x)
              ( map-hom-Ab (ab-Ring R1) (ab-Ring R2) f y))))

preserves-unit-hom-Ab :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
  hom-Ab (ab-Ring R1) (ab-Ring R2) → UU l2
preserves-unit-hom-Ab R1 R2 f =
  Id (map-hom-Ab (ab-Ring R1) (ab-Ring R2) f (unit-Ring R1)) (unit-Ring R2)

is-prop-preserves-unit-hom-Ab :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
  ( f : hom-Ab (ab-Ring R1) (ab-Ring R2)) →
  is-prop (preserves-unit-hom-Ab R1 R2 f)
is-prop-preserves-unit-hom-Ab R1 R2 f =
  is-set-type-Ring R2
    ( map-hom-Ab (ab-Ring R1) (ab-Ring R2) f (unit-Ring R1))
    ( unit-Ring R2)

is-ring-homomorphism-hom-Ab :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
  ( f : hom-Ab (ab-Ring R1) (ab-Ring R2)) → UU (l1 ⊔ l2)
is-ring-homomorphism-hom-Ab R1 R2 f =
  preserves-mul-hom-Ab R1 R2 f × preserves-unit-hom-Ab R1 R2 f

is-prop-is-ring-homomorphism-hom-Ab :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
  ( f : hom-Ab (ab-Ring R1) (ab-Ring R2)) →
  is-prop (is-ring-homomorphism-hom-Ab R1 R2 f)
is-prop-is-ring-homomorphism-hom-Ab R1 R2 f =
  is-prop-prod
    ( is-prop-preserves-mul-hom-Ab R1 R2 f)
    ( is-prop-preserves-unit-hom-Ab R1 R2 f)

hom-Ring :
  {l1 l2 : Level} (R1 : Ring l1) (R : Ring l2) → UU (l1 ⊔ l2)
hom-Ring R1 R2 =
  Σ (hom-Ab (ab-Ring R1) (ab-Ring R2)) (is-ring-homomorphism-hom-Ab R1 R2)

{- Basic infrastructure for ring homomorphisms. -}

hom-Ab-hom-Ring :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
  hom-Ring R1 R2 → hom-Ab (ab-Ring R1) (ab-Ring R2)
hom-Ab-hom-Ring R1 R2 = pr1

map-hom-Ring :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
  hom-Ring R1 R2 → type-Ring R1 → type-Ring R2
map-hom-Ring R1 R2 f =
  map-hom-Ab (ab-Ring R1) (ab-Ring R2) (hom-Ab-hom-Ring R1 R2 f)

preserves-add-hom-Ring :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
  (f : hom-Ring R1 R2) →
  preserves-add (ab-Ring R1) (ab-Ring R2) (map-hom-Ring R1 R2 f)
preserves-add-hom-Ring R1 R2 f =
  preserves-add-Ab (ab-Ring R1) (ab-Ring R2) (hom-Ab-hom-Ring R1 R2 f)

preserves-mul-hom-Ring :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
  (f : hom-Ring R1 R2) → preserves-mul-hom-Ab R1 R2 (hom-Ab-hom-Ring R1 R2 f)
preserves-mul-hom-Ring R1 R2 f = pr1 (pr2 f)

preserves-unit-hom-Ring :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
  (f : hom-Ring R1 R2) → preserves-unit-hom-Ab R1 R2 (hom-Ab-hom-Ring R1 R2 f)
preserves-unit-hom-Ring R1 R2 f = pr2 (pr2 f)

is-ring-homomorphism-hom-Ring :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
  (f : hom-Ring R1 R2) →
  prod ( preserves-mul-hom-Ab R1 R2 (hom-Ab-hom-Ring R1 R2 f))
       ( preserves-unit-hom-Ab R1 R2 (hom-Ab-hom-Ring R1 R2 f))
is-ring-homomorphism-hom-Ring R1 R2 f =
  pair ( preserves-mul-hom-Ring R1 R2 f)
       ( preserves-unit-hom-Ring R1 R2 f)
```

```agda
{- We characterize the identity type of ring homomorphisms -}

htpy-hom-Ring :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
  hom-Ring R1 R2 → hom-Ring R1 R2 → UU (l1 ⊔ l2)
htpy-hom-Ring R1 R2 f g = map-hom-Ring R1 R2 f ~ map-hom-Ring R1 R2 g

reflexive-htpy-hom-Ring :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
  (f : hom-Ring R1 R2) → htpy-hom-Ring R1 R2 f f
reflexive-htpy-hom-Ring R1 R2 f = refl-htpy

htpy-hom-Ring-eq :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
  (f g : hom-Ring R1 R2) → Id f g → htpy-hom-Ring R1 R2 f g
htpy-hom-Ring-eq R1 R2 f .f refl = reflexive-htpy-hom-Ring R1 R2 f

is-contr-total-htpy-hom-Ring :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) (f : hom-Ring R1 R2) →
  is-contr (Σ (hom-Ring R1 R2) (htpy-hom-Ring R1 R2 f))
is-contr-total-htpy-hom-Ring R1 R2 f =
  is-contr-total-Eq-subtype
    ( is-contr-total-htpy-hom-Ab
      ( ab-Ring R1)
      ( ab-Ring R2)
      ( hom-Ab-hom-Ring R1 R2 f))
    ( is-prop-is-ring-homomorphism-hom-Ab R1 R2)
    ( hom-Ab-hom-Ring R1 R2 f)
    ( reflexive-htpy-hom-Ring R1 R2 f)
    ( is-ring-homomorphism-hom-Ring R1 R2 f)

is-equiv-htpy-hom-Ring-eq :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) (f g : hom-Ring R1 R2) →
  is-equiv (htpy-hom-Ring-eq R1 R2 f g)
is-equiv-htpy-hom-Ring-eq R1 R2 f =
  fundamental-theorem-id f
    ( reflexive-htpy-hom-Ring R1 R2 f)
    ( is-contr-total-htpy-hom-Ring R1 R2 f)
    ( htpy-hom-Ring-eq R1 R2 f)

equiv-htpy-hom-Ring-eq :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) (f g : hom-Ring R1 R2) →
  Id f g ≃ htpy-hom-Ring R1 R2 f g
equiv-htpy-hom-Ring-eq R1 R2 f g =
  pair
    ( htpy-hom-Ring-eq R1 R2 f g)
    ( is-equiv-htpy-hom-Ring-eq R1 R2 f g)

eq-htpy-hom-Ring :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) (f g : hom-Ring R1 R2) →
  htpy-hom-Ring R1 R2 f g → Id f g
eq-htpy-hom-Ring R1 R2 f g =
  map-inv-is-equiv (is-equiv-htpy-hom-Ring-eq R1 R2 f g)

is-set-hom-Ring :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) → is-set (hom-Ring R1 R2)
is-set-hom-Ring R1 R2 =
  is-trunc-is-subtype
    ( neg-one-𝕋)
    ( is-prop-is-ring-homomorphism-hom-Ab R1 R2)
    ( is-set-hom-Ab (ab-Ring R1) (ab-Ring R2))

hom-ring-Set :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) → UU-Set (l1 ⊔ l2)
pr1 (hom-ring-Set R1 R2) = hom-Ring R1 R2
pr2 (hom-ring-Set R1 R2) = is-set-hom-Ring R1 R2

{- We define the categorical structure of rings -}

preserves-mul-id-hom-Ring :
  {l : Level} (R : Ring l) → preserves-mul-hom-Ab R R (id-hom-Ab (ab-Ring R))
preserves-mul-id-hom-Ring R x y = refl

preserves-unit-id-hom-Ring :
  {l : Level} (R : Ring l) → preserves-unit-hom-Ab R R (id-hom-Ab (ab-Ring R))
preserves-unit-id-hom-Ring R = refl

is-ring-homomorphism-id-hom-Ring :
  {l : Level} (R : Ring l) → is-ring-homomorphism-hom-Ab R R (id-hom-Ab (ab-Ring R))
is-ring-homomorphism-id-hom-Ring R =
  pair (preserves-mul-id-hom-Ring R) (preserves-unit-id-hom-Ring R)

id-hom-Ring :
  {l : Level} (R : Ring l) → hom-Ring R R
id-hom-Ring R = pair (id-hom-Ab (ab-Ring R)) (is-ring-homomorphism-id-hom-Ring R)

hom-Ab-comp-hom-Ring :
  { l1 l2 l3 : Level} (R1 : Ring l1) (R2 : Ring l2) (R3 : Ring l3) →
  ( g : hom-Ring R2 R3) (f : hom-Ring R1 R2) →
  hom-Ab (ab-Ring R1) (ab-Ring R3) 
hom-Ab-comp-hom-Ring R1 R2 R3 g f =
  comp-hom-Ab
    ( ab-Ring R1)
    ( ab-Ring R2)
    ( ab-Ring R3)
    ( hom-Ab-hom-Ring R2 R3 g)
    ( hom-Ab-hom-Ring R1 R2 f)

preserves-mul-comp-hom-Ring :
  { l1 l2 l3 : Level} (R1 : Ring l1) (R2 : Ring l2) (R3 : Ring l3) →
  ( g : hom-Ring R2 R3) (f : hom-Ring R1 R2) →
  preserves-mul-hom-Ab R1 R3 (hom-Ab-comp-hom-Ring R1 R2 R3 g f)
preserves-mul-comp-hom-Ring R1 R2 R3 g f x y =
  ( ap (map-hom-Ring R2 R3 g) (preserves-mul-hom-Ring R1 R2 f x y)) ∙
  ( preserves-mul-hom-Ring R2 R3 g
    ( map-hom-Ring R1 R2 f x)
    ( map-hom-Ring R1 R2 f y))

preserves-unit-comp-hom-Ring :
  { l1 l2 l3 : Level} (R1 : Ring l1) (R2 : Ring l2) (R3 : Ring l3) →
  ( g : hom-Ring R2 R3) (f : hom-Ring R1 R2) →
  preserves-unit-hom-Ab R1 R3 (hom-Ab-comp-hom-Ring R1 R2 R3 g f)
preserves-unit-comp-hom-Ring R1 R2 R3 g f =
  ( ap (map-hom-Ring R2 R3 g) (preserves-unit-hom-Ring R1 R2 f)) ∙
  ( preserves-unit-hom-Ring R2 R3 g)

is-ring-homomorphism-comp-hom-Ring :
  { l1 l2 l3 : Level} (R1 : Ring l1) (R2 : Ring l2) (R3 : Ring l3) →
  ( g : hom-Ring R2 R3) (f : hom-Ring R1 R2) →
  is-ring-homomorphism-hom-Ab R1 R3 (hom-Ab-comp-hom-Ring R1 R2 R3 g f)
is-ring-homomorphism-comp-hom-Ring R1 R2 R3 g f =
  pair ( preserves-mul-comp-hom-Ring R1 R2 R3 g f)
       ( preserves-unit-comp-hom-Ring R1 R2 R3 g f)

comp-hom-Ring :
  { l1 l2 l3 : Level} (R1 : Ring l1) (R2 : Ring l2) (R3 : Ring l3) →
  hom-Ring R2 R3 → hom-Ring R1 R2 → hom-Ring R1 R3
comp-hom-Ring R1 R2 R3 g f =
  pair ( hom-Ab-comp-hom-Ring R1 R2 R3 g f)
       ( is-ring-homomorphism-comp-hom-Ring R1 R2 R3 g f)

{- We prove the laws of a category for Rings -}

is-associative-comp-hom-Ring :
  { l1 l2 l3 l4 : Level}
  ( R1 : Ring l1) (R2 : Ring l2) (R3 : Ring l3) (R4 : Ring l4) →
  ( h : hom-Ring R3 R4) (g : hom-Ring R2 R3) (f : hom-Ring R1 R2) →
  Id (comp-hom-Ring R1 R2 R4 (comp-hom-Ring R2 R3 R4 h g) f)
     (comp-hom-Ring R1 R3 R4 h (comp-hom-Ring R1 R2 R3 g f))
is-associative-comp-hom-Ring R1 R2 R3 R4 h g f =
  eq-htpy-hom-Ring R1 R4
    ( comp-hom-Ring R1 R2 R4 (comp-hom-Ring R2 R3 R4 h g) f)
    ( comp-hom-Ring R1 R3 R4 h (comp-hom-Ring R1 R2 R3 g f))
    ( refl-htpy)

left-unit-law-comp-hom-Ring :
  { l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) (f : hom-Ring R1 R2) →
  Id (comp-hom-Ring R1 R2 R2 (id-hom-Ring R2) f) f
left-unit-law-comp-hom-Ring R1 R2 f =
  eq-htpy-hom-Ring R1 R2
    ( comp-hom-Ring R1 R2 R2 (id-hom-Ring R2) f)
    ( f)
    ( refl-htpy)

right-unit-law-comp-hom-Ring :
  { l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) (f : hom-Ring R1 R2) →
  Id (comp-hom-Ring R1 R1 R2 f (id-hom-Ring R1)) f
right-unit-law-comp-hom-Ring R1 R2 f =
  eq-htpy-hom-Ring R1 R2
    ( comp-hom-Ring R1 R1 R2 f (id-hom-Ring R1))
    ( f)
    ( refl-htpy)
```
