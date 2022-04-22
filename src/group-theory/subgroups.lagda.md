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
    is-prop-function-type; is-prop-prod; is-prop-is-equiv; Π-Prop; hom-Prop;
    prod-Prop)
open import foundation.raising-universe-levels using (raise-Prop)
open import foundation.sets using (is-set; is-set-function-type; UU-Set)
open import foundation.subtypes using
  ( subtype; is-emb-inclusion-subtype; type-subtype; inclusion-subtype;
    is-set-type-subtype)
open import foundation.unit-type using (unit-Prop; star; raise-star)
open import foundation.universe-levels using (Level; UU; lsuc; _⊔_)

open import group-theory.groups using
  ( Group; type-Group; unit-Group; mul-Group; inv-Group; is-set-type-Group;
    associative-mul-Group; left-unit-law-Group; right-unit-law-Group;
    left-inverse-law-Group; right-inverse-law-Group; is-unit-group-Prop;
    is-own-inverse-unit-Group)
open import group-theory.homomorphisms-groups using
  ( preserves-mul-Group; type-hom-Group; preserves-unit-Group;
    preserves-inverses-Group)
open import group-theory.semigroups using (Semigroup)
```

## Definitions

### Subsets of subgroups

```agda
subset-Group :
  (l : Level) {l1 : Level} (G : Group l1) → UU ((lsuc l) ⊔ l1)
subset-Group l G = subtype l (type-Group G)

is-set-subset-Group :
  (l : Level) {l1 : Level} (G : Group l1) → is-set (subset-Group l G)
is-set-subset-Group l G =
  is-set-function-type is-set-UU-Prop
```

### Subgroups

```agda
module _
  {l1 l2 : Level} (G : Group l1) (P : subset-Group l2 G)
  where
  
  contains-unit-subset-group-Prop : UU-Prop l2
  contains-unit-subset-group-Prop = P (unit-Group G)
  
  contains-unit-subset-Group : UU l2
  contains-unit-subset-Group = type-Prop contains-unit-subset-group-Prop

  is-prop-contains-unit-subset-Group : is-prop contains-unit-subset-Group
  is-prop-contains-unit-subset-Group =
    is-prop-type-Prop contains-unit-subset-group-Prop

  is-closed-under-mul-subset-group-Prop : UU-Prop (l1 ⊔ l2)
  is-closed-under-mul-subset-group-Prop =
    Π-Prop
      ( type-Group G)
      ( λ x →
        Π-Prop
          ( type-Group G)
          ( λ y → hom-Prop (P x) (hom-Prop (P y) (P (mul-Group G x y)))))

  is-closed-under-mul-subset-Group : UU (l1 ⊔ l2)
  is-closed-under-mul-subset-Group =
    type-Prop is-closed-under-mul-subset-group-Prop

  is-prop-is-closed-under-mul-subset-Group :
    is-prop is-closed-under-mul-subset-Group
  is-prop-is-closed-under-mul-subset-Group =
    is-prop-type-Prop is-closed-under-mul-subset-group-Prop

  is-closed-under-inv-subset-group-Prop : UU-Prop (l1 ⊔ l2)
  is-closed-under-inv-subset-group-Prop =
    Π-Prop
      ( type-Group G)
      ( λ x → hom-Prop (P x) (P (inv-Group G x)))

  is-closed-under-inv-subset-Group : UU (l1 ⊔ l2)
  is-closed-under-inv-subset-Group =
    type-Prop is-closed-under-inv-subset-group-Prop

  is-prop-is-closed-under-inv-subset-Group :
    is-prop is-closed-under-inv-subset-Group
  is-prop-is-closed-under-inv-subset-Group =
    is-prop-type-Prop is-closed-under-inv-subset-group-Prop

  is-subgroup-subset-group-Prop : UU-Prop (l1 ⊔ l2)
  is-subgroup-subset-group-Prop =
    prod-Prop
      ( contains-unit-subset-group-Prop)
      ( prod-Prop
        ( is-closed-under-mul-subset-group-Prop)
        ( is-closed-under-inv-subset-group-Prop))

  is-subgroup-subset-Group : UU (l1 ⊔ l2)
  is-subgroup-subset-Group = type-Prop is-subgroup-subset-group-Prop

  is-prop-is-subgroup-subset-Group : is-prop is-subgroup-subset-Group
  is-prop-is-subgroup-subset-Group =
    is-prop-type-Prop is-subgroup-subset-group-Prop

Subgroup :
  (l : Level) {l1 : Level} (G : Group l1) → UU ((lsuc l) ⊔ l1)
Subgroup l G = type-subtype (is-subgroup-subset-group-Prop {l2 = l} G)

module _
  {l1 l2 : Level} (G : Group l1) (H : Subgroup l2 G)
  where

  subset-Subgroup : subset-Group l2 G
  subset-Subgroup = inclusion-subtype (is-subgroup-subset-group-Prop G) H

  type-Subgroup : UU (l1 ⊔ l2)
  type-Subgroup = type-subtype subset-Subgroup

  map-inclusion-Subgroup : type-Subgroup → type-Group G
  map-inclusion-Subgroup = inclusion-subtype subset-Subgroup

  type-predicate-Subgroup : type-Group G → UU l2
  type-predicate-Subgroup x = type-Prop (subset-Subgroup x)

  is-prop-type-predicate-Subgroup :
    (x : type-Group G) → is-prop (type-predicate-Subgroup x)
  is-prop-type-predicate-Subgroup x = is-prop-type-Prop (subset-Subgroup x)

  is-subgroup-Subgroup : is-subgroup-subset-Group G subset-Subgroup
  is-subgroup-Subgroup = pr2 H

  contains-unit-Subgroup :
    contains-unit-subset-Group G subset-Subgroup
  contains-unit-Subgroup = pr1 is-subgroup-Subgroup

  is-closed-under-mul-Subgroup :
    is-closed-under-mul-subset-Group G subset-Subgroup
  is-closed-under-mul-Subgroup = pr1 (pr2 is-subgroup-Subgroup)

  is-closed-under-inv-Subgroup :
    is-closed-under-inv-subset-Group G subset-Subgroup
  is-closed-under-inv-Subgroup = pr2 (pr2 is-subgroup-Subgroup)

is-emb-subset-Subgroup :
  {l1 l2 : Level} (G : Group l1) → is-emb (subset-Subgroup {l2 = l2} G)
is-emb-subset-Subgroup G =
  is-emb-inclusion-subtype (is-subgroup-subset-group-Prop G)
```

### The underlying group of a subgroup

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Subgroup l2 G)
  where
  
  type-group-Subgroup :  UU (l1 ⊔ l2)
  type-group-Subgroup = type-subtype (subset-Subgroup G H)

  map-inclusion-group-Subgroup : type-group-Subgroup → type-Group G
  map-inclusion-group-Subgroup = inclusion-subtype (subset-Subgroup G H)

  is-emb-inclusion-group-Subgroup : is-emb map-inclusion-group-Subgroup
  is-emb-inclusion-group-Subgroup =
    is-emb-inclusion-subtype (subset-Subgroup G H)

  eq-subgroup-eq-group :
    {x y : type-group-Subgroup} →
    Id (map-inclusion-group-Subgroup x) (map-inclusion-group-Subgroup y) →
    Id x y
  eq-subgroup-eq-group {x} {y} =
    map-inv-is-equiv (is-emb-inclusion-group-Subgroup x y)

  set-group-Subgroup : UU-Set (l1 ⊔ l2)
  pr1 set-group-Subgroup = type-group-Subgroup
  pr2 set-group-Subgroup =
    is-set-type-subtype (subset-Subgroup G H) (is-set-type-Group G)

  mul-group-Subgroup : (x y : type-group-Subgroup) → type-group-Subgroup
  pr1 (mul-group-Subgroup x y) = mul-Group G (pr1 x) (pr1 y)
  pr2 (mul-group-Subgroup x y) =
    is-closed-under-mul-Subgroup G H (pr1 x) (pr1 y) (pr2 x) (pr2 y)

  associative-mul-group-Subgroup :
    (x y z : type-group-Subgroup) →
    Id (mul-group-Subgroup (mul-group-Subgroup x y) z)
       (mul-group-Subgroup x (mul-group-Subgroup y z))
  associative-mul-group-Subgroup x y z =
    eq-subgroup-eq-group (associative-mul-Group G (pr1 x) (pr1 y) (pr1 z))

  unit-group-Subgroup : type-group-Subgroup
  pr1 unit-group-Subgroup = unit-Group G
  pr2 unit-group-Subgroup = contains-unit-Subgroup G H

  left-unit-law-group-Subgroup :
    (x : type-group-Subgroup) → Id (mul-group-Subgroup unit-group-Subgroup x) x
  left-unit-law-group-Subgroup x =
    eq-subgroup-eq-group (left-unit-law-Group G (pr1 x))

  right-unit-law-group-Subgroup :
    (x : type-group-Subgroup) → Id (mul-group-Subgroup x unit-group-Subgroup) x
  right-unit-law-group-Subgroup x =
    eq-subgroup-eq-group (right-unit-law-Group G (pr1 x))

  inv-group-Subgroup : type-group-Subgroup → type-group-Subgroup
  pr1 (inv-group-Subgroup x) = inv-Group G (pr1 x)
  pr2 (inv-group-Subgroup x) = is-closed-under-inv-Subgroup G H (pr1 x) (pr2 x)

  left-inverse-law-group-Subgroup :
    ( x : type-group-Subgroup) →
    Id ( mul-group-Subgroup (inv-group-Subgroup x) x)
       ( unit-group-Subgroup)
  left-inverse-law-group-Subgroup x =
    eq-subgroup-eq-group (left-inverse-law-Group G (pr1 x))

  right-inverse-law-group-Subgroup :
    (x : type-group-Subgroup) →
    Id ( mul-group-Subgroup x (inv-group-Subgroup x))
       ( unit-group-Subgroup)
  right-inverse-law-group-Subgroup x =
    eq-subgroup-eq-group (right-inverse-law-Group G (pr1 x))

  semigroup-Subgroup : Semigroup (l1 ⊔ l2)
  pr1 semigroup-Subgroup = set-group-Subgroup
  pr1 (pr2 semigroup-Subgroup) = mul-group-Subgroup
  pr2 (pr2 semigroup-Subgroup) = associative-mul-group-Subgroup

  group-Subgroup : Group (l1 ⊔ l2)
  pr1 group-Subgroup = semigroup-Subgroup
  pr1 (pr1 (pr2 group-Subgroup)) = unit-group-Subgroup
  pr1 (pr2 (pr1 (pr2 group-Subgroup))) = left-unit-law-group-Subgroup
  pr2 (pr2 (pr1 (pr2 group-Subgroup))) = right-unit-law-group-Subgroup
  pr1 (pr2 (pr2 group-Subgroup)) = inv-group-Subgroup
  pr1 (pr2 (pr2 (pr2 group-Subgroup))) = left-inverse-law-group-Subgroup
  pr2 (pr2 (pr2 (pr2 group-Subgroup))) = right-inverse-law-group-Subgroup
```

### The inclusion of the underlying group of a subgroup into the ambient group

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Subgroup l2 G)
  where
  
  preserves-mul-inclusion-group-Subgroup :
    preserves-mul-Group
      ( group-Subgroup G H)
      ( G)
      ( map-inclusion-group-Subgroup G H)
  preserves-mul-inclusion-group-Subgroup x y = refl

  preserves-unit-inclusion-group-Subgroup :
    preserves-unit-Group
      ( group-Subgroup G H)
      ( G)
      ( map-inclusion-group-Subgroup G H)
  preserves-unit-inclusion-group-Subgroup = refl

  preserves-inverses-inclusion-group-Subgroup :
    preserves-inverses-Group
      ( group-Subgroup G H)
      ( G)
      ( map-inclusion-group-Subgroup G H)
  preserves-inverses-inclusion-group-Subgroup x = refl

  inclusion-group-Subgroup : type-hom-Group (group-Subgroup G H) G
  pr1 inclusion-group-Subgroup = map-inclusion-group-Subgroup G H
  pr2 inclusion-group-Subgroup = preserves-mul-inclusion-group-Subgroup
```

### Examples of subgroups

```agda
module _
  {l1 l2 : Level} (G : Group l1)
  where

  complete-Subgroup : Subgroup l2 G
  pr1 complete-Subgroup x = raise-Prop l2 unit-Prop
  pr1 (pr2 complete-Subgroup) = raise-star
  pr1 (pr2 (pr2 complete-Subgroup)) _ _ _ _ = raise-star
  pr2 (pr2 (pr2 complete-Subgroup)) _ _ = raise-star

  trivial-Subgroup : Subgroup l1 G
  pr1 trivial-Subgroup x = is-unit-group-Prop G x
  pr1 (pr2 trivial-Subgroup) = refl
  pr1 (pr2 (pr2 trivial-Subgroup)) .(unit-Group G) .(unit-Group G) refl refl =
    left-unit-law-Group G (unit-Group G)
  pr2 (pr2 (pr2 trivial-Subgroup)) .(unit-Group G) refl =
    is-own-inverse-unit-Group G
```


