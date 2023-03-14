# Ring homomorphisms

```agda
module ring-theory.homomorphisms-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtype-identity-principle
open import foundation.subtypes
open import foundation.truncation-levels
open import foundation.universe-levels

open import group-theory.homomorphisms-abelian-groups

open import ring-theory.rings
```

</details>

## Idea

Ring homomorphisms are maps between rings that preserve the ring structure

## Definition

```agda
{- Ring homomorphisms -}

preserves-mul-hom-Ab :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
  type-hom-Ab (ab-Ring R1) (ab-Ring R2) → UU (l1 ⊔ l2)
preserves-mul-hom-Ab R1 R2 f =
  (x y : type-Ring R1) →
  Id ( map-hom-Ab (ab-Ring R1) (ab-Ring R2) f (mul-Ring R1 x y))
     ( mul-Ring R2
       ( map-hom-Ab (ab-Ring R1) (ab-Ring R2) f x)
       ( map-hom-Ab (ab-Ring R1) (ab-Ring R2) f y))

is-prop-preserves-mul-hom-Ab :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
  ( f : type-hom-Ab (ab-Ring R1) (ab-Ring R2)) →
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

preserves-one-hom-Ab :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
  type-hom-Ab (ab-Ring R1) (ab-Ring R2) → UU l2
preserves-one-hom-Ab R1 R2 f =
  Id (map-hom-Ab (ab-Ring R1) (ab-Ring R2) f (one-Ring R1)) (one-Ring R2)

is-prop-preserves-one-hom-Ab :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
  ( f : type-hom-Ab (ab-Ring R1) (ab-Ring R2)) →
  is-prop (preserves-one-hom-Ab R1 R2 f)
is-prop-preserves-one-hom-Ab R1 R2 f =
  is-set-type-Ring R2
    ( map-hom-Ab (ab-Ring R1) (ab-Ring R2) f (one-Ring R1))
    ( one-Ring R2)

is-ring-homomorphism-hom-Ab :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
  ( f : type-hom-Ab (ab-Ring R1) (ab-Ring R2)) → UU (l1 ⊔ l2)
is-ring-homomorphism-hom-Ab R1 R2 f =
  preserves-mul-hom-Ab R1 R2 f × preserves-one-hom-Ab R1 R2 f

is-prop-is-ring-homomorphism-hom-Ab :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
  ( f : type-hom-Ab (ab-Ring R1) (ab-Ring R2)) →
  is-prop (is-ring-homomorphism-hom-Ab R1 R2 f)
is-prop-is-ring-homomorphism-hom-Ab R1 R2 f =
  is-prop-prod
    ( is-prop-preserves-mul-hom-Ab R1 R2 f)
    ( is-prop-preserves-one-hom-Ab R1 R2 f)

is-ring-homomorphism-hom-ab-Prop :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
  (f : type-hom-Ab (ab-Ring R1) (ab-Ring R2)) → Prop (l1 ⊔ l2)
pr1 (is-ring-homomorphism-hom-ab-Prop R1 R2 f) =
  is-ring-homomorphism-hom-Ab R1 R2 f
pr2 (is-ring-homomorphism-hom-ab-Prop R1 R2 f) =
  is-prop-is-ring-homomorphism-hom-Ab R1 R2 f

type-hom-Ring :
  {l1 l2 : Level} (R1 : Ring l1) (R : Ring l2) → UU (l1 ⊔ l2)
type-hom-Ring R1 R2 =
  Σ (type-hom-Ab (ab-Ring R1) (ab-Ring R2)) (is-ring-homomorphism-hom-Ab R1 R2)

{- Basic infrastructure for ring homomorphisms. -}

hom-ab-hom-Ring :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
  type-hom-Ring R1 R2 → type-hom-Ab (ab-Ring R1) (ab-Ring R2)
hom-ab-hom-Ring R1 R2 = pr1

map-hom-Ring :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
  type-hom-Ring R1 R2 → type-Ring R1 → type-Ring R2
map-hom-Ring R1 R2 f =
  map-hom-Ab (ab-Ring R1) (ab-Ring R2) (hom-ab-hom-Ring R1 R2 f)

preserves-add-hom-Ring :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
  (f : type-hom-Ring R1 R2) →
  preserves-add-Ab (ab-Ring R1) (ab-Ring R2) (map-hom-Ring R1 R2 f)
preserves-add-hom-Ring R1 R2 f =
  preserves-add-hom-Ab (ab-Ring R1) (ab-Ring R2) (hom-ab-hom-Ring R1 R2 f)

preserves-zero-hom-Ring :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
  (f : type-hom-Ring R1 R2) →
  preserves-zero-Ab (ab-Ring R1) (ab-Ring R2) (map-hom-Ring R1 R2 f)
preserves-zero-hom-Ring R1 R2 f =
  preserves-zero-hom-Ab (ab-Ring R1) (ab-Ring R2) (hom-ab-hom-Ring R1 R2 f)

preserves-neg-hom-Ring :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
  (f : type-hom-Ring R1 R2) →
  preserves-negatives-Ab (ab-Ring R1) (ab-Ring R2) (map-hom-Ring R1 R2 f)
preserves-neg-hom-Ring R1 R2 f =
  preserves-negatives-hom-Ab (ab-Ring R1) (ab-Ring R2) (hom-ab-hom-Ring R1 R2 f)

preserves-mul-hom-Ring :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
  (f : type-hom-Ring R1 R2) → preserves-mul-hom-Ab R1 R2 (hom-ab-hom-Ring R1 R2 f)
preserves-mul-hom-Ring R1 R2 f = pr1 (pr2 f)

preserves-one-hom-Ring :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
  (f : type-hom-Ring R1 R2) → preserves-one-hom-Ab R1 R2 (hom-ab-hom-Ring R1 R2 f)
preserves-one-hom-Ring R1 R2 f = pr2 (pr2 f)

is-ring-homomorphism-hom-Ring :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
  (f : type-hom-Ring R1 R2) →
  ( preserves-mul-hom-Ab R1 R2 (hom-ab-hom-Ring R1 R2 f)) ×
  ( preserves-one-hom-Ab R1 R2 (hom-ab-hom-Ring R1 R2 f))
is-ring-homomorphism-hom-Ring R1 R2 f =
  pair ( preserves-mul-hom-Ring R1 R2 f)
       ( preserves-one-hom-Ring R1 R2 f)
```

```agda
{- We characterize the identity type of ring homomorphisms -}

htpy-hom-Ring :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
  type-hom-Ring R1 R2 → type-hom-Ring R1 R2 → UU (l1 ⊔ l2)
htpy-hom-Ring R1 R2 f g = map-hom-Ring R1 R2 f ~ map-hom-Ring R1 R2 g

reflexive-htpy-hom-Ring :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
  (f : type-hom-Ring R1 R2) → htpy-hom-Ring R1 R2 f f
reflexive-htpy-hom-Ring R1 R2 f = refl-htpy

htpy-eq-hom-Ring :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
  (f g : type-hom-Ring R1 R2) → Id f g → htpy-hom-Ring R1 R2 f g
htpy-eq-hom-Ring R1 R2 f .f refl = reflexive-htpy-hom-Ring R1 R2 f

is-contr-total-htpy-hom-Ring :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) (f : type-hom-Ring R1 R2) →
  is-contr (Σ (type-hom-Ring R1 R2) (htpy-hom-Ring R1 R2 f))
is-contr-total-htpy-hom-Ring R1 R2 f =
  is-contr-total-Eq-subtype
    ( is-contr-total-htpy-hom-Ab
      ( ab-Ring R1)
      ( ab-Ring R2)
      ( hom-ab-hom-Ring R1 R2 f))
    ( is-prop-is-ring-homomorphism-hom-Ab R1 R2)
    ( hom-ab-hom-Ring R1 R2 f)
    ( reflexive-htpy-hom-Ring R1 R2 f)
    ( is-ring-homomorphism-hom-Ring R1 R2 f)

is-equiv-htpy-eq-hom-Ring :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) (f g : type-hom-Ring R1 R2) →
  is-equiv (htpy-eq-hom-Ring R1 R2 f g)
is-equiv-htpy-eq-hom-Ring R1 R2 f =
  fundamental-theorem-id
    ( is-contr-total-htpy-hom-Ring R1 R2 f)
    ( htpy-eq-hom-Ring R1 R2 f)

equiv-htpy-eq-hom-Ring :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) (f g : type-hom-Ring R1 R2) →
  Id f g ≃ htpy-hom-Ring R1 R2 f g
equiv-htpy-eq-hom-Ring R1 R2 f g =
  pair
    ( htpy-eq-hom-Ring R1 R2 f g)
    ( is-equiv-htpy-eq-hom-Ring R1 R2 f g)

eq-htpy-hom-Ring :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) (f g : type-hom-Ring R1 R2) →
  htpy-hom-Ring R1 R2 f g → Id f g
eq-htpy-hom-Ring R1 R2 f g =
  map-inv-is-equiv (is-equiv-htpy-eq-hom-Ring R1 R2 f g)

is-set-type-hom-Ring :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) → is-set (type-hom-Ring R1 R2)
is-set-type-hom-Ring R1 R2 =
  is-trunc-type-subtype
    ( neg-one-𝕋)
    ( is-ring-homomorphism-hom-ab-Prop R1 R2)
    ( is-set-hom-Ab (ab-Ring R1) (ab-Ring R2))

hom-Ring :
  {l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) → Set (l1 ⊔ l2)
pr1 (hom-Ring R1 R2) = type-hom-Ring R1 R2
pr2 (hom-Ring R1 R2) = is-set-type-hom-Ring R1 R2

{- We define the categorical structure of rings -}

preserves-mul-id-hom-Ring :
  {l : Level} (R : Ring l) → preserves-mul-hom-Ab R R (id-hom-Ab (ab-Ring R))
preserves-mul-id-hom-Ring R x y = refl

preserves-one-id-hom-Ring :
  {l : Level} (R : Ring l) → preserves-one-hom-Ab R R (id-hom-Ab (ab-Ring R))
preserves-one-id-hom-Ring R = refl

is-ring-homomorphism-id-hom-Ring :
  {l : Level} (R : Ring l) → is-ring-homomorphism-hom-Ab R R (id-hom-Ab (ab-Ring R))
is-ring-homomorphism-id-hom-Ring R =
  pair (preserves-mul-id-hom-Ring R) (preserves-one-id-hom-Ring R)

id-hom-Ring :
  {l : Level} (R : Ring l) → type-hom-Ring R R
id-hom-Ring R = pair (id-hom-Ab (ab-Ring R)) (is-ring-homomorphism-id-hom-Ring R)

hom-Ab-comp-hom-Ring :
  { l1 l2 l3 : Level} (R1 : Ring l1) (R2 : Ring l2) (R3 : Ring l3) →
  ( g : type-hom-Ring R2 R3) (f : type-hom-Ring R1 R2) →
  type-hom-Ab (ab-Ring R1) (ab-Ring R3)
hom-Ab-comp-hom-Ring R1 R2 R3 g f =
  comp-hom-Ab
    ( ab-Ring R1)
    ( ab-Ring R2)
    ( ab-Ring R3)
    ( hom-ab-hom-Ring R2 R3 g)
    ( hom-ab-hom-Ring R1 R2 f)

preserves-mul-comp-hom-Ring :
  { l1 l2 l3 : Level} (R1 : Ring l1) (R2 : Ring l2) (R3 : Ring l3) →
  ( g : type-hom-Ring R2 R3) (f : type-hom-Ring R1 R2) →
  preserves-mul-hom-Ab R1 R3 (hom-Ab-comp-hom-Ring R1 R2 R3 g f)
preserves-mul-comp-hom-Ring R1 R2 R3 g f x y =
  ( ap (map-hom-Ring R2 R3 g) (preserves-mul-hom-Ring R1 R2 f x y)) ∙
  ( preserves-mul-hom-Ring R2 R3 g
    ( map-hom-Ring R1 R2 f x)
    ( map-hom-Ring R1 R2 f y))

preserves-one-comp-hom-Ring :
  { l1 l2 l3 : Level} (R1 : Ring l1) (R2 : Ring l2) (R3 : Ring l3) →
  ( g : type-hom-Ring R2 R3) (f : type-hom-Ring R1 R2) →
  preserves-one-hom-Ab R1 R3 (hom-Ab-comp-hom-Ring R1 R2 R3 g f)
preserves-one-comp-hom-Ring R1 R2 R3 g f =
  ( ap (map-hom-Ring R2 R3 g) (preserves-one-hom-Ring R1 R2 f)) ∙
  ( preserves-one-hom-Ring R2 R3 g)

is-ring-homomorphism-comp-hom-Ring :
  { l1 l2 l3 : Level} (R1 : Ring l1) (R2 : Ring l2) (R3 : Ring l3) →
  ( g : type-hom-Ring R2 R3) (f : type-hom-Ring R1 R2) →
  is-ring-homomorphism-hom-Ab R1 R3 (hom-Ab-comp-hom-Ring R1 R2 R3 g f)
is-ring-homomorphism-comp-hom-Ring R1 R2 R3 g f =
  pair ( preserves-mul-comp-hom-Ring R1 R2 R3 g f)
       ( preserves-one-comp-hom-Ring R1 R2 R3 g f)

comp-hom-Ring :
  { l1 l2 l3 : Level} (R1 : Ring l1) (R2 : Ring l2) (R3 : Ring l3) →
  type-hom-Ring R2 R3 → type-hom-Ring R1 R2 → type-hom-Ring R1 R3
comp-hom-Ring R1 R2 R3 g f =
  pair ( hom-Ab-comp-hom-Ring R1 R2 R3 g f)
       ( is-ring-homomorphism-comp-hom-Ring R1 R2 R3 g f)

{- We prove the laws of a category for Rings -}

is-associative-comp-hom-Ring :
  { l1 l2 l3 l4 : Level}
  ( R1 : Ring l1) (R2 : Ring l2) (R3 : Ring l3) (R4 : Ring l4) →
  ( h : type-hom-Ring R3 R4) (g : type-hom-Ring R2 R3) (f : type-hom-Ring R1 R2) →
  Id (comp-hom-Ring R1 R2 R4 (comp-hom-Ring R2 R3 R4 h g) f)
     (comp-hom-Ring R1 R3 R4 h (comp-hom-Ring R1 R2 R3 g f))
is-associative-comp-hom-Ring R1 R2 R3 R4 h g f =
  eq-htpy-hom-Ring R1 R4
    ( comp-hom-Ring R1 R2 R4 (comp-hom-Ring R2 R3 R4 h g) f)
    ( comp-hom-Ring R1 R3 R4 h (comp-hom-Ring R1 R2 R3 g f))
    ( refl-htpy)

left-unit-law-comp-hom-Ring :
  { l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) (f : type-hom-Ring R1 R2) →
  Id (comp-hom-Ring R1 R2 R2 (id-hom-Ring R2) f) f
left-unit-law-comp-hom-Ring R1 R2 f =
  eq-htpy-hom-Ring R1 R2
    ( comp-hom-Ring R1 R2 R2 (id-hom-Ring R2) f)
    ( f)
    ( refl-htpy)

right-unit-law-comp-hom-Ring :
  { l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) (f : type-hom-Ring R1 R2) →
  Id (comp-hom-Ring R1 R1 R2 f (id-hom-Ring R1)) f
right-unit-law-comp-hom-Ring R1 R2 f =
  eq-htpy-hom-Ring R1 R2
    ( comp-hom-Ring R1 R1 R2 f (id-hom-Ring R1))
    ( f)
    ( refl-htpy)
```

```agda
id-law-ab-Ring :
  { l1 : Level} (R1 : Ring l1) →
  Id (hom-ab-hom-Ring R1 R1 (id-hom-Ring R1)) (id-hom-Ab (ab-Ring R1))
id-law-ab-Ring R1 =
  eq-htpy-hom-Ab
    ( ab-Ring R1)
    ( ab-Ring R1)
    ( refl-htpy)

comp-law-ab-Ring :
  { l1 l2 l3 : Level} (R1 : Ring l1) (R2 : Ring l2) (R3 : Ring l3) →
  ( g : type-hom-Ring R2 R3) (f : type-hom-Ring R1 R2) →
  Id ( hom-ab-hom-Ring R1 R3 (comp-hom-Ring R1 R2 R3 g f))
     ( comp-hom-Ab
       ( ab-Ring R1)
       ( ab-Ring R2)
       ( ab-Ring R3)
       ( hom-ab-hom-Ring R2 R3 g)
       ( hom-ab-hom-Ring R1 R2 f))
comp-law-ab-Ring R1 R2 R3 g f =
  eq-htpy-hom-Ab
    ( ab-Ring R1)
    ( ab-Ring R3)
    ( refl-htpy)
```
