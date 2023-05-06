# Ring homomorphisms

```agda
module ring-theory.homomorphisms-rings where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategories

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

## Definitions

```agda
preserves-mul-hom-Ab :
  {l1 l2 : Level} (R : Ring l1) (S : Ring l2) →
  type-hom-Ab (ab-Ring R) (ab-Ring S) → UU (l1 ⊔ l2)
preserves-mul-hom-Ab R S f =
  (x y : type-Ring R) →
  Id ( map-hom-Ab (ab-Ring R) (ab-Ring S) f (mul-Ring R x y))
     ( mul-Ring S
       ( map-hom-Ab (ab-Ring R) (ab-Ring S) f x)
       ( map-hom-Ab (ab-Ring R) (ab-Ring S) f y))

is-prop-preserves-mul-hom-Ab :
  {l1 l2 : Level} (R : Ring l1) (S : Ring l2) →
  ( f : type-hom-Ab (ab-Ring R) (ab-Ring S)) →
  is-prop (preserves-mul-hom-Ab R S f)
is-prop-preserves-mul-hom-Ab R S f =
  is-prop-Π
    ( λ x →
      is-prop-Π
        ( λ y →
          is-set-type-Ring S
            ( map-hom-Ab (ab-Ring R) (ab-Ring S) f (mul-Ring R x y))
            ( mul-Ring S
              ( map-hom-Ab (ab-Ring R) (ab-Ring S) f x)
              ( map-hom-Ab (ab-Ring R) (ab-Ring S) f y))))

preserves-one-hom-Ab :
  {l1 l2 : Level} (R : Ring l1) (S : Ring l2) →
  type-hom-Ab (ab-Ring R) (ab-Ring S) → UU l2
preserves-one-hom-Ab R S f =
  Id (map-hom-Ab (ab-Ring R) (ab-Ring S) f (one-Ring R)) (one-Ring S)

is-prop-preserves-one-hom-Ab :
  {l1 l2 : Level} (R : Ring l1) (S : Ring l2) →
  ( f : type-hom-Ab (ab-Ring R) (ab-Ring S)) →
  is-prop (preserves-one-hom-Ab R S f)
is-prop-preserves-one-hom-Ab R S f =
  is-set-type-Ring S
    ( map-hom-Ab (ab-Ring R) (ab-Ring S) f (one-Ring R))
    ( one-Ring S)

is-ring-homomorphism-hom-Ab :
  {l1 l2 : Level} (R : Ring l1) (S : Ring l2) →
  ( f : type-hom-Ab (ab-Ring R) (ab-Ring S)) → UU (l1 ⊔ l2)
is-ring-homomorphism-hom-Ab R S f =
  preserves-mul-hom-Ab R S f × preserves-one-hom-Ab R S f

is-prop-is-ring-homomorphism-hom-Ab :
  {l1 l2 : Level} (R : Ring l1) (S : Ring l2) →
  ( f : type-hom-Ab (ab-Ring R) (ab-Ring S)) →
  is-prop (is-ring-homomorphism-hom-Ab R S f)
is-prop-is-ring-homomorphism-hom-Ab R S f =
  is-prop-prod
    ( is-prop-preserves-mul-hom-Ab R S f)
    ( is-prop-preserves-one-hom-Ab R S f)

is-ring-homomorphism-hom-ab-Prop :
  {l1 l2 : Level} (R : Ring l1) (S : Ring l2) →
  (f : type-hom-Ab (ab-Ring R) (ab-Ring S)) → Prop (l1 ⊔ l2)
pr1 (is-ring-homomorphism-hom-ab-Prop R S f) =
  is-ring-homomorphism-hom-Ab R S f
pr2 (is-ring-homomorphism-hom-ab-Prop R S f) =
  is-prop-is-ring-homomorphism-hom-Ab R S f

type-hom-Ring :
  {l1 l2 : Level} (R : Ring l1) (R : Ring l2) → UU (l1 ⊔ l2)
type-hom-Ring R S =
  Σ (type-hom-Ab (ab-Ring R) (ab-Ring S)) (is-ring-homomorphism-hom-Ab R S)
```

### Components of a ring homomorphism

```agda
hom-ab-hom-Ring :
  {l1 l2 : Level} (R : Ring l1) (S : Ring l2) →
  type-hom-Ring R S → type-hom-Ab (ab-Ring R) (ab-Ring S)
hom-ab-hom-Ring R S = pr1

map-hom-Ring :
  {l1 l2 : Level} (R : Ring l1) (S : Ring l2) →
  type-hom-Ring R S → type-Ring R → type-Ring S
map-hom-Ring R S f =
  map-hom-Ab (ab-Ring R) (ab-Ring S) (hom-ab-hom-Ring R S f)

preserves-add-hom-Ring :
  {l1 l2 : Level} (R : Ring l1) (S : Ring l2) →
  (f : type-hom-Ring R S) →
  preserves-add-Ab (ab-Ring R) (ab-Ring S) (map-hom-Ring R S f)
preserves-add-hom-Ring R S f =
  preserves-add-hom-Ab (ab-Ring R) (ab-Ring S) (hom-ab-hom-Ring R S f)

preserves-zero-hom-Ring :
  {l1 l2 : Level} (R : Ring l1) (S : Ring l2) →
  (f : type-hom-Ring R S) →
  preserves-zero-Ab (ab-Ring R) (ab-Ring S) (map-hom-Ring R S f)
preserves-zero-hom-Ring R S f =
  preserves-zero-hom-Ab (ab-Ring R) (ab-Ring S) (hom-ab-hom-Ring R S f)

preserves-neg-hom-Ring :
  {l1 l2 : Level} (R : Ring l1) (S : Ring l2) →
  (f : type-hom-Ring R S) →
  preserves-negatives-Ab (ab-Ring R) (ab-Ring S) (map-hom-Ring R S f)
preserves-neg-hom-Ring R S f =
  preserves-negatives-hom-Ab (ab-Ring R) (ab-Ring S) (hom-ab-hom-Ring R S f)

preserves-mul-hom-Ring :
  {l1 l2 : Level} (R : Ring l1) (S : Ring l2) →
  (f : type-hom-Ring R S) →
  preserves-mul-hom-Ab R S (hom-ab-hom-Ring R S f)
preserves-mul-hom-Ring R S f = pr1 (pr2 f)

preserves-one-hom-Ring :
  {l1 l2 : Level} (R : Ring l1) (S : Ring l2) →
  (f : type-hom-Ring R S) →
  preserves-one-hom-Ab R S (hom-ab-hom-Ring R S f)
preserves-one-hom-Ring R S f = pr2 (pr2 f)

is-ring-homomorphism-hom-Ring :
  {l1 l2 : Level} (R : Ring l1) (S : Ring l2) →
  (f : type-hom-Ring R S) →
  ( preserves-mul-hom-Ab R S (hom-ab-hom-Ring R S f)) ×
  ( preserves-one-hom-Ab R S (hom-ab-hom-Ring R S f))
is-ring-homomorphism-hom-Ring R S f =
  pair ( preserves-mul-hom-Ring R S f)
       ( preserves-one-hom-Ring R S f)
```

## Properties

### Characterizing the identity type of ring homomorphisms

```agda
htpy-hom-Ring :
  {l1 l2 : Level} (R : Ring l1) (S : Ring l2) →
  type-hom-Ring R S → type-hom-Ring R S → UU (l1 ⊔ l2)
htpy-hom-Ring R S f g = map-hom-Ring R S f ~ map-hom-Ring R S g

reflexive-htpy-hom-Ring :
  {l1 l2 : Level} (R : Ring l1) (S : Ring l2) →
  (f : type-hom-Ring R S) → htpy-hom-Ring R S f f
reflexive-htpy-hom-Ring R S f = refl-htpy

htpy-eq-hom-Ring :
  {l1 l2 : Level} (R : Ring l1) (S : Ring l2) →
  (f g : type-hom-Ring R S) → Id f g → htpy-hom-Ring R S f g
htpy-eq-hom-Ring R S f .f refl = reflexive-htpy-hom-Ring R S f

is-contr-total-htpy-hom-Ring :
  {l1 l2 : Level} (R : Ring l1) (S : Ring l2) (f : type-hom-Ring R S) →
  is-contr (Σ (type-hom-Ring R S) (htpy-hom-Ring R S f))
is-contr-total-htpy-hom-Ring R S f =
  is-contr-total-Eq-subtype
    ( is-contr-total-htpy-hom-Ab
      ( ab-Ring R)
      ( ab-Ring S)
      ( hom-ab-hom-Ring R S f))
    ( is-prop-is-ring-homomorphism-hom-Ab R S)
    ( hom-ab-hom-Ring R S f)
    ( reflexive-htpy-hom-Ring R S f)
    ( is-ring-homomorphism-hom-Ring R S f)

is-equiv-htpy-eq-hom-Ring :
  {l1 l2 : Level} (R : Ring l1) (S : Ring l2) (f g : type-hom-Ring R S) →
  is-equiv (htpy-eq-hom-Ring R S f g)
is-equiv-htpy-eq-hom-Ring R S f =
  fundamental-theorem-id
    ( is-contr-total-htpy-hom-Ring R S f)
    ( htpy-eq-hom-Ring R S f)

equiv-htpy-eq-hom-Ring :
  {l1 l2 : Level} (R : Ring l1) (S : Ring l2) (f g : type-hom-Ring R S) →
  Id f g ≃ htpy-hom-Ring R S f g
equiv-htpy-eq-hom-Ring R S f g =
  pair
    ( htpy-eq-hom-Ring R S f g)
    ( is-equiv-htpy-eq-hom-Ring R S f g)

eq-htpy-hom-Ring :
  {l1 l2 : Level} (R : Ring l1) (S : Ring l2) (f g : type-hom-Ring R S) →
  htpy-hom-Ring R S f g → Id f g
eq-htpy-hom-Ring R S f g =
  map-inv-is-equiv (is-equiv-htpy-eq-hom-Ring R S f g)

is-set-type-hom-Ring :
  {l1 l2 : Level} (R : Ring l1) (S : Ring l2) → is-set (type-hom-Ring R S)
is-set-type-hom-Ring R S =
  is-trunc-type-subtype
    ( neg-one-𝕋)
    ( is-ring-homomorphism-hom-ab-Prop R S)
    ( is-set-hom-Ab (ab-Ring R) (ab-Ring S))

hom-Ring :
  {l1 l2 : Level} (R : Ring l1) (S : Ring l2) → Set (l1 ⊔ l2)
pr1 (hom-Ring R S) = type-hom-Ring R S
pr2 (hom-Ring R S) = is-set-type-hom-Ring R S
```

### Rings form a precategory

```agda
preserves-mul-id-hom-Ring :
  {l : Level} (R : Ring l) → preserves-mul-hom-Ab R R (id-hom-Ab (ab-Ring R))
preserves-mul-id-hom-Ring R x y = refl

preserves-one-id-hom-Ring :
  {l : Level} (R : Ring l) → preserves-one-hom-Ab R R (id-hom-Ab (ab-Ring R))
preserves-one-id-hom-Ring R = refl

is-ring-homomorphism-id-hom-Ring :
  {l : Level} (R : Ring l) →
  is-ring-homomorphism-hom-Ab R R (id-hom-Ab (ab-Ring R))
is-ring-homomorphism-id-hom-Ring R =
  pair (preserves-mul-id-hom-Ring R) (preserves-one-id-hom-Ring R)

id-hom-Ring :
  {l : Level} (R : Ring l) → type-hom-Ring R R
id-hom-Ring R =
  pair (id-hom-Ab (ab-Ring R)) (is-ring-homomorphism-id-hom-Ring R)

hom-Ab-comp-hom-Ring :
  { l1 l2 l3 : Level} (R : Ring l1) (S : Ring l2) (T : Ring l3) →
  ( g : type-hom-Ring S T) (f : type-hom-Ring R S) →
  type-hom-Ab (ab-Ring R) (ab-Ring T)
hom-Ab-comp-hom-Ring R S T g f =
  comp-hom-Ab
    ( ab-Ring R)
    ( ab-Ring S)
    ( ab-Ring T)
    ( hom-ab-hom-Ring S T g)
    ( hom-ab-hom-Ring R S f)

preserves-mul-comp-hom-Ring :
  { l1 l2 l3 : Level} (R : Ring l1) (S : Ring l2) (T : Ring l3) →
  ( g : type-hom-Ring S T) (f : type-hom-Ring R S) →
  preserves-mul-hom-Ab R T (hom-Ab-comp-hom-Ring R S T g f)
preserves-mul-comp-hom-Ring R S T g f x y =
  ( ap (map-hom-Ring S T g) (preserves-mul-hom-Ring R S f x y)) ∙
  ( preserves-mul-hom-Ring S T g
    ( map-hom-Ring R S f x)
    ( map-hom-Ring R S f y))

preserves-one-comp-hom-Ring :
  { l1 l2 l3 : Level} (R : Ring l1) (S : Ring l2) (T : Ring l3) →
  ( g : type-hom-Ring S T) (f : type-hom-Ring R S) →
  preserves-one-hom-Ab R T (hom-Ab-comp-hom-Ring R S T g f)
preserves-one-comp-hom-Ring R S T g f =
  ( ap (map-hom-Ring S T g) (preserves-one-hom-Ring R S f)) ∙
  ( preserves-one-hom-Ring S T g)

is-ring-homomorphism-comp-hom-Ring :
  { l1 l2 l3 : Level} (R : Ring l1) (S : Ring l2) (T : Ring l3) →
  ( g : type-hom-Ring S T) (f : type-hom-Ring R S) →
  is-ring-homomorphism-hom-Ab R T (hom-Ab-comp-hom-Ring R S T g f)
is-ring-homomorphism-comp-hom-Ring R S T g f =
  pair ( preserves-mul-comp-hom-Ring R S T g f)
       ( preserves-one-comp-hom-Ring R S T g f)

comp-hom-Ring :
  { l1 l2 l3 : Level} (R : Ring l1) (S : Ring l2) (T : Ring l3) →
  type-hom-Ring S T → type-hom-Ring R S → type-hom-Ring R T
comp-hom-Ring R S T g f =
  pair ( hom-Ab-comp-hom-Ring R S T g f)
       ( is-ring-homomorphism-comp-hom-Ring R S T g f)
```

```agda
associative-comp-hom-Ring :
  { l1 l2 l3 l4 : Level}
  ( R : Ring l1) (S : Ring l2) (T : Ring l3) (U : Ring l4) →
  ( h : type-hom-Ring T U)
  ( g : type-hom-Ring S T)
  ( f : type-hom-Ring R S) →
  Id (comp-hom-Ring R S U (comp-hom-Ring S T U h g) f)
     (comp-hom-Ring R T U h (comp-hom-Ring R S T g f))
associative-comp-hom-Ring R S T U h g f =
  eq-htpy-hom-Ring R U
    ( comp-hom-Ring R S U (comp-hom-Ring S T U h g) f)
    ( comp-hom-Ring R T U h (comp-hom-Ring R S T g f))
    ( refl-htpy)

left-unit-law-comp-hom-Ring :
  { l1 l2 : Level} (R : Ring l1) (S : Ring l2) (f : type-hom-Ring R S) →
  Id (comp-hom-Ring R S S (id-hom-Ring S) f) f
left-unit-law-comp-hom-Ring R S f =
  eq-htpy-hom-Ring R S
    ( comp-hom-Ring R S S (id-hom-Ring S) f)
    ( f)
    ( refl-htpy)

right-unit-law-comp-hom-Ring :
  { l1 l2 : Level} (R : Ring l1) (S : Ring l2) (f : type-hom-Ring R S) →
  Id (comp-hom-Ring R R S f (id-hom-Ring R)) f
right-unit-law-comp-hom-Ring R S f =
  eq-htpy-hom-Ring R S
    ( comp-hom-Ring R R S f (id-hom-Ring R))
    ( f)
    ( refl-htpy)
```

```agda
id-law-ab-Ring :
  { l1 : Level} (R : Ring l1) →
  Id (hom-ab-hom-Ring R R (id-hom-Ring R)) (id-hom-Ab (ab-Ring R))
id-law-ab-Ring R =
  eq-htpy-hom-Ab
    ( ab-Ring R)
    ( ab-Ring R)
    ( refl-htpy)

comp-law-ab-Ring :
  { l1 l2 l3 : Level} (R : Ring l1) (S : Ring l2) (T : Ring l3) →
  ( g : type-hom-Ring S T) (f : type-hom-Ring R S) →
  Id ( hom-ab-hom-Ring R T (comp-hom-Ring R S T g f))
     ( comp-hom-Ab
       ( ab-Ring R)
       ( ab-Ring S)
       ( ab-Ring T)
       ( hom-ab-hom-Ring S T g)
       ( hom-ab-hom-Ring R S f))
comp-law-ab-Ring R S T g f =
  eq-htpy-hom-Ab
    ( ab-Ring R)
    ( ab-Ring T)
    ( refl-htpy)
```
