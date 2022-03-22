# Subgroups

```agda
{-# OPTIONS --without-K --exact-split #-}

module group-theory.subgroups where

open import foundation.cartesian-product-types using (_×_)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.embeddings using (is-emb)
open import foundation.equivalences using (map-inv-is-equiv)
open import foundation.identity-types using (Id; refl)
open import foundation.propositional-extensionality using (is-set-UU-Prop)
open import foundation.propositions using
  ( UU-Prop; type-Prop; is-prop; is-prop-type-Prop; is-prop-Π;
    is-prop-function-type; is-prop-prod; is-prop-is-equiv)
open import foundation.sets using (is-set; is-set-function-type; UU-Set)
open import foundation.subtypes using (is-emb-pr1)
open import foundation.universe-levels using (Level; UU; lsuc; _⊔_)

open import group-theory.groups using
  ( Group; type-Group; unit-Group; mul-Group; inv-Group; is-set-type-Group;
    associative-mul-Group; left-unit-law-Group; right-unit-law-Group;
    left-inverse-law-Group; right-inverse-law-Group)
open import group-theory.homomorphisms-groups using
  ( preserves-mul-Group; type-hom-Group)
```

## Definitions

### Subsets of subgroups

```agda
subset-Group :
  (l : Level) {l1 : Level} (G : Group l1) → UU ((lsuc l) ⊔ l1)
subset-Group l G = type-Group G → UU-Prop l

is-set-subset-Group :
  (l : Level) {l1 : Level} (G : Group l1) → is-set (subset-Group l G)
is-set-subset-Group l G =
  is-set-function-type is-set-UU-Prop
```

### Subgroups

```agda
contains-unit-subset-Group :
  {l1 l2 : Level} (G : Group l1) (P : subset-Group l2 G) → UU l2
contains-unit-subset-Group G P = type-Prop (P (unit-Group G))

is-prop-contains-unit-subset-Group :
  {l1 l2 : Level} (G : Group l1) (P : subset-Group l2 G) →
  is-prop (contains-unit-subset-Group G P)
is-prop-contains-unit-subset-Group G P = is-prop-type-Prop (P (unit-Group G))

closed-under-mul-subset-Group :
  {l1 l2 : Level} (G : Group l1) (P : subset-Group l2 G) → UU (l1 ⊔ l2)
closed-under-mul-subset-Group G P =
  (x y : type-Group G) →
  type-Prop (P x) → type-Prop (P y) → type-Prop (P (mul-Group G x y))

is-prop-closed-under-mul-subset-Group :
  {l1 l2 : Level} (G : Group l1) (P : subset-Group l2 G) →
  is-prop (closed-under-mul-subset-Group G P)
is-prop-closed-under-mul-subset-Group G P =
  is-prop-Π (λ x →
    is-prop-Π (λ y →
      is-prop-function-type
        ( is-prop-function-type
          ( is-prop-type-Prop (P (mul-Group G x y))))))

closed-under-inv-subset-Group :
  {l1 l2 : Level} (G : Group l1) (P : subset-Group l2 G) → UU (l1 ⊔ l2)
closed-under-inv-subset-Group G P =
  (x : type-Group G) → type-Prop (P x) → type-Prop (P (inv-Group G x))

is-prop-closed-under-inv-subset-Group :
  {l1 l2 : Level} (G : Group l1) (P : subset-Group l2 G) →
  is-prop (closed-under-inv-subset-Group G P)
is-prop-closed-under-inv-subset-Group G P =
  is-prop-Π
    ( λ x → is-prop-function-type (is-prop-type-Prop (P (inv-Group G x))))

is-subgroup-Group :
  {l1 l2 : Level} (G : Group l1) (P : subset-Group l2 G) → UU (l1 ⊔ l2)
is-subgroup-Group G P =
  ( contains-unit-subset-Group G P) ×
  ( ( closed-under-mul-subset-Group G P) ×
    ( closed-under-inv-subset-Group G P))

is-prop-is-subgroup-Group :
  {l1 l2 : Level} (G : Group l1) (P : subset-Group l2 G) →
  is-prop (is-subgroup-Group G P)
is-prop-is-subgroup-Group G P =
  is-prop-prod
    ( is-prop-contains-unit-subset-Group G P)
    ( is-prop-prod
      ( is-prop-closed-under-mul-subset-Group G P)
      ( is-prop-closed-under-inv-subset-Group G P))

Subgroup :
  (l : Level) {l1 : Level} (G : Group l1) → UU ((lsuc l) ⊔ l1)
Subgroup l G = Σ (type-Group G → UU-Prop l) (is-subgroup-Group G)

subset-Subgroup :
  {l1 l2 : Level} (G : Group l1) →
  ( Subgroup l2 G) → ( subset-Group l2 G)
subset-Subgroup G = pr1

is-emb-subset-Subgroup :
  {l1 l2 : Level} (G : Group l1) → is-emb (subset-Subgroup {l2 = l2} G)
is-emb-subset-Subgroup G = is-emb-pr1 (is-prop-is-subgroup-Group G)

type-subset-Subgroup :
  {l1 l2 : Level} (G : Group l1) (P : Subgroup l2 G) →
  (type-Group G → UU l2)
type-subset-Subgroup G P x = type-Prop (subset-Subgroup G P x)

is-prop-type-subset-Subgroup :
  {l1 l2 : Level} (G : Group l1) (P : Subgroup l2 G) →
  (x : type-Group G) → is-prop (type-subset-Subgroup G P x)
is-prop-type-subset-Subgroup G P x =
  is-prop-type-Prop (subset-Subgroup G P x)

is-subgroup-Subgroup :
  {l1 l2 : Level} (G : Group l1) (P : Subgroup l2 G) →
  is-subgroup-Group G (subset-Subgroup G P)
is-subgroup-Subgroup G = pr2

contains-unit-Subgroup :
  {l1 l2 : Level} (G : Group l1) (P : Subgroup l2 G) →
  contains-unit-subset-Group G (subset-Subgroup G P)
contains-unit-Subgroup G P = pr1 (is-subgroup-Subgroup G P)

closed-under-mul-Subgroup :
  {l1 l2 : Level} (G : Group l1) (P : Subgroup l2 G) →
  closed-under-mul-subset-Group G (subset-Subgroup G P)
closed-under-mul-Subgroup G P = pr1 (pr2 (is-subgroup-Subgroup G P))

closed-under-inv-Subgroup :
  {l1 l2 : Level} (G : Group l1) (P : Subgroup l2 G) →
  closed-under-inv-subset-Group G (subset-Subgroup G P)
closed-under-inv-Subgroup G P = pr2 (pr2 (is-subgroup-Subgroup G P))
```

### The underlying group of a subgroup

```agda
type-group-Subgroup :
  {l1 l2 : Level} (G : Group l1) (P : Subgroup l2 G) → UU (l1 ⊔ l2)
type-group-Subgroup G P =
  Σ (type-Group G) (type-subset-Subgroup G P)

incl-group-Subgroup :
  {l1 l2 : Level} (G : Group l1) (P : Subgroup l2 G) →
  type-group-Subgroup G P → type-Group G
incl-group-Subgroup G P = pr1

is-emb-incl-group-Subgroup :
  {l1 l2 : Level} (G : Group l1) (P : Subgroup l2 G) →
  is-emb (incl-group-Subgroup G P)
is-emb-incl-group-Subgroup G P =
  is-emb-pr1 (is-prop-type-subset-Subgroup G P)

eq-subgroup-eq-group :
  {l1 l2 : Level} (G : Group l1) (P : Subgroup l2 G) →
  {x y : type-group-Subgroup G P} →
  Id (incl-group-Subgroup G P x) (incl-group-Subgroup G P y) → Id x y
eq-subgroup-eq-group G P {x} {y} =
  map-inv-is-equiv (is-emb-incl-group-Subgroup G P x y)

set-group-Subgroup :
  {l1 l2 : Level} (G : Group l1) → Subgroup l2 G → UU-Set (l1 ⊔ l2)
set-group-Subgroup G P =
  pair ( type-group-Subgroup G P)
       ( λ x y →
         is-prop-is-equiv
           ( is-emb-incl-group-Subgroup G P x y)
           ( is-set-type-Group G (pr1 x) (pr1 y)))

unit-group-Subgroup :
  {l1 l2 : Level} (G : Group l1) (P : Subgroup l2 G) → type-group-Subgroup G P
unit-group-Subgroup G P =
  pair ( unit-Group G)
       ( contains-unit-Subgroup G P)

mul-group-Subgroup :
  {l1 l2 : Level} (G : Group l1) (P : Subgroup l2 G) →
  ( x y : type-group-Subgroup G P) → type-group-Subgroup G P
mul-group-Subgroup G P x y =
  pair ( mul-Group G (pr1 x) (pr1 y))
       ( closed-under-mul-Subgroup G P (pr1 x) (pr1 y) (pr2 x) (pr2 y))

inv-group-Subgroup :
  {l1 l2 : Level} (G : Group l1) (P : Subgroup l2 G) →
  type-group-Subgroup G P → type-group-Subgroup G P
inv-group-Subgroup G P x =
  pair (inv-Group G (pr1 x)) (closed-under-inv-Subgroup G P (pr1 x) (pr2 x))

associative-mul-group-Subgroup :
  {l1 l2 : Level} (G : Group l1) (P : Subgroup l2 G) →
  ( x y z : type-group-Subgroup G P) →
  Id (mul-group-Subgroup G P (mul-group-Subgroup G P x y) z)
     (mul-group-Subgroup G P x (mul-group-Subgroup G P y z))
associative-mul-group-Subgroup G P x y z =
  eq-subgroup-eq-group G P (associative-mul-Group G (pr1 x) (pr1 y) (pr1 z))

left-unit-law-group-Subgroup :
  {l1 l2 : Level} (G : Group l1) (P : Subgroup l2 G) →
  ( x : type-group-Subgroup G P) →
  Id (mul-group-Subgroup G P (unit-group-Subgroup G P) x) x
left-unit-law-group-Subgroup G P x =
  eq-subgroup-eq-group G P (left-unit-law-Group G (pr1 x))

right-unit-law-group-Subgroup :
  {l1 l2 : Level} (G : Group l1) (P : Subgroup l2 G) →
  ( x : type-group-Subgroup G P) →
  Id (mul-group-Subgroup G P x (unit-group-Subgroup G P)) x
right-unit-law-group-Subgroup G P x =
  eq-subgroup-eq-group G P (right-unit-law-Group G (pr1 x))

left-inverse-law-group-Subgroup :
  {l1 l2 : Level} (G : Group l1) (P : Subgroup l2 G) →
  ( x : type-group-Subgroup G P) →
  Id ( mul-group-Subgroup G P (inv-group-Subgroup G P x) x)
     ( unit-group-Subgroup G P)
left-inverse-law-group-Subgroup G P x =
  eq-subgroup-eq-group G P (left-inverse-law-Group G (pr1 x))

right-inverse-law-group-Subgroup :
  {l1 l2 : Level} (G : Group l1) (P : Subgroup l2 G) →
  ( x : type-group-Subgroup G P) →
  Id ( mul-group-Subgroup G P x (inv-group-Subgroup G P x))
     ( unit-group-Subgroup G P)
right-inverse-law-group-Subgroup G P x =
  eq-subgroup-eq-group G P (right-inverse-law-Group G (pr1 x))

group-Subgroup :
  {l1 l2 : Level} (G : Group l1) → Subgroup l2 G → Group (l1 ⊔ l2)
group-Subgroup G P =
  pair
    ( pair
      ( set-group-Subgroup G P)
      ( pair
        ( mul-group-Subgroup G P)
        ( associative-mul-group-Subgroup G P)))
    ( pair
      ( pair
        ( unit-group-Subgroup G P)
        ( pair
          ( left-unit-law-group-Subgroup G P)
          ( right-unit-law-group-Subgroup G P)))
      ( pair
        ( inv-group-Subgroup G P)
        ( pair
          ( left-inverse-law-group-Subgroup G P)
          ( right-inverse-law-group-Subgroup G P))))
```

### The inclusion of the underlying group of a subgroup into the ambient group

```agda
preserves-mul-incl-group-Subgroup :
  { l1 l2 : Level} (G : Group l1) (P : Subgroup l2 G) →
  preserves-mul-Group (group-Subgroup G P) G (incl-group-Subgroup G P)
preserves-mul-incl-group-Subgroup G P (pair x p) (pair y q) = refl

hom-group-Subgroup :
  { l1 l2 : Level} (G : Group l1) (P : Subgroup l2 G) →
  type-hom-Group (group-Subgroup G P) G
hom-group-Subgroup G P =
  pair (incl-group-Subgroup G P) (preserves-mul-incl-group-Subgroup G P)
```
