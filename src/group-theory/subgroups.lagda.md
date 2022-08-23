---
title: Subgroups
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module group-theory.subgroups where

open import foundation.binary-relations using
  ( is-reflexive-Rel-Prop; is-symmetric-Rel-Prop; is-transitive-Rel-Prop)
open import foundation.cartesian-product-types using (_×_)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2; _,_)
open import foundation.embeddings using (is-emb; _↪_; is-emb-comp')
open import foundation.equality-dependent-pair-types using (eq-pair-Σ)
open import foundation.equivalence-relations using (Eq-Rel)
open import foundation.equivalences using (map-inv-is-equiv; _≃_)
open import foundation.fibers-of-maps using (fib)
open import foundation.function-extensionality using (eq-htpy)
open import foundation.functions using (id; _∘_)
open import foundation.identity-types using (Id; refl; inv; _∙_; ap; _＝_)
open import foundation.powersets using (_⊆_)
open import foundation.propositional-extensionality using (is-set-UU-Prop)
open import foundation.propositional-maps using (is-prop-map-is-emb)
open import foundation.propositions using
  ( UU-Prop; type-Prop; is-prop; is-prop-type-Prop; is-prop-Π;
    is-prop-function-type; is-prop-prod; is-prop-is-equiv; Π-Prop; hom-Prop;
    prod-Prop; eq-is-prop)
open import foundation.raising-universe-levels using (raise-Prop; map-raise)
open import foundation.sets using (is-set; is-set-function-type; UU-Set)
open import foundation.subtype-identity-principle using
  ( extensionality-type-subtype)
open import foundation.subtypes using
  ( subtype; is-emb-inclusion-subtype; type-subtype; inclusion-subtype;
    is-set-type-subtype; is-prop-is-in-subtype; is-in-subtype; emb-subtype;
    has-same-elements-subtype; extensionality-subtype)
open import foundation.unit-type using (unit-Prop; star; raise-star)
open import foundation.universe-levels using (Level; UU; lsuc; _⊔_)

open import group-theory.groups using
  ( Group; type-Group; unit-Group; mul-Group; inv-Group; is-set-type-Group;
    associative-mul-Group; left-unit-law-mul-Group; right-unit-law-mul-Group;
    left-inverse-law-mul-Group; right-inverse-law-mul-Group; is-unit-group-Prop;
    inv-unit-Group; semigroup-Group; is-emb-mul-Group; transpose-eq-mul-Group;
    mul-Group'; is-emb-mul-Group'; transpose-eq-mul-Group')
open import group-theory.homomorphisms-groups using
  ( preserves-mul-Group; type-hom-Group; preserves-unit-Group;
    preserves-inverses-Group)
open import group-theory.homomorphisms-semigroups using (is-prop-preserves-mul-Semigroup)
open import group-theory.isomorphisms-groups using
  ( type-iso-Group; comp-iso-Group)
open import group-theory.semigroups using (Semigroup)
```

## Definitions

### Subsets of groups

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

  inclusion-Subgroup : type-Subgroup → type-Group G
  inclusion-Subgroup = inclusion-subtype subset-Subgroup

  is-emb-inclusion-Subgroup : is-emb inclusion-Subgroup
  is-emb-inclusion-Subgroup = is-emb-inclusion-subtype subset-Subgroup

  emb-inclusion-Subgroup : type-Subgroup ↪ type-Group G
  emb-inclusion-Subgroup = emb-subtype subset-Subgroup

  is-in-Subgroup : type-Group G → UU l2
  is-in-Subgroup = is-in-subtype subset-Subgroup

  is-in-subgroup-inclusion-Subgroup :
    (x : type-Subgroup) → is-in-Subgroup (inclusion-Subgroup x)
  is-in-subgroup-inclusion-Subgroup x = pr2 x

  is-prop-is-in-Subgroup :
    (x : type-Group G) → is-prop (is-in-Subgroup x)
  is-prop-is-in-Subgroup = is-prop-is-in-subtype subset-Subgroup

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

  mul-Subgroup : (x y : type-group-Subgroup) → type-group-Subgroup
  pr1 (mul-Subgroup x y) = mul-Group G (pr1 x) (pr1 y)
  pr2 (mul-Subgroup x y) =
    is-closed-under-mul-Subgroup G H (pr1 x) (pr1 y) (pr2 x) (pr2 y)

  associative-mul-Subgroup :
    (x y z : type-group-Subgroup) →
    Id (mul-Subgroup (mul-Subgroup x y) z)
       (mul-Subgroup x (mul-Subgroup y z))
  associative-mul-Subgroup x y z =
    eq-subgroup-eq-group (associative-mul-Group G (pr1 x) (pr1 y) (pr1 z))

  unit-Subgroup : type-group-Subgroup
  pr1 unit-Subgroup = unit-Group G
  pr2 unit-Subgroup = contains-unit-Subgroup G H

  left-unit-law-mul-Subgroup :
    (x : type-group-Subgroup) → Id (mul-Subgroup unit-Subgroup x) x
  left-unit-law-mul-Subgroup x =
    eq-subgroup-eq-group (left-unit-law-mul-Group G (pr1 x))

  right-unit-law-mul-Subgroup :
    (x : type-group-Subgroup) → Id (mul-Subgroup x unit-Subgroup) x
  right-unit-law-mul-Subgroup x =
    eq-subgroup-eq-group (right-unit-law-mul-Group G (pr1 x))

  inv-Subgroup : type-group-Subgroup → type-group-Subgroup
  pr1 (inv-Subgroup x) = inv-Group G (pr1 x)
  pr2 (inv-Subgroup x) = is-closed-under-inv-Subgroup G H (pr1 x) (pr2 x)

  left-inverse-law-mul-Subgroup :
    ( x : type-group-Subgroup) →
    Id ( mul-Subgroup (inv-Subgroup x) x)
       ( unit-Subgroup)
  left-inverse-law-mul-Subgroup x =
    eq-subgroup-eq-group (left-inverse-law-mul-Group G (pr1 x))

  right-inverse-law-mul-Subgroup :
    (x : type-group-Subgroup) →
    Id ( mul-Subgroup x (inv-Subgroup x))
       ( unit-Subgroup)
  right-inverse-law-mul-Subgroup x =
    eq-subgroup-eq-group (right-inverse-law-mul-Group G (pr1 x))

  semigroup-Subgroup : Semigroup (l1 ⊔ l2)
  pr1 semigroup-Subgroup = set-group-Subgroup
  pr1 (pr2 semigroup-Subgroup) = mul-Subgroup
  pr2 (pr2 semigroup-Subgroup) = associative-mul-Subgroup

  group-Subgroup : Group (l1 ⊔ l2)
  pr1 group-Subgroup = semigroup-Subgroup
  pr1 (pr1 (pr2 group-Subgroup)) = unit-Subgroup
  pr1 (pr2 (pr1 (pr2 group-Subgroup))) = left-unit-law-mul-Subgroup
  pr2 (pr2 (pr1 (pr2 group-Subgroup))) = right-unit-law-mul-Subgroup
  pr1 (pr2 (pr2 group-Subgroup)) = inv-Subgroup
  pr1 (pr2 (pr2 (pr2 group-Subgroup))) = left-inverse-law-mul-Subgroup
  pr2 (pr2 (pr2 (pr2 group-Subgroup))) = right-inverse-law-mul-Subgroup
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

## Properties

### Extensionality of the type of all subgroups

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Subgroup l2 G)
  where

  has-same-elements-Subgroup : {l3 : Level} → Subgroup l3 G → UU (l1 ⊔ l2 ⊔ l3)
  has-same-elements-Subgroup K =
    has-same-elements-subtype (subset-Subgroup G H) (subset-Subgroup G K)

  extensionality-Subgroup :
    (K : Subgroup l2 G) → (H ＝ K) ≃ has-same-elements-Subgroup K
  extensionality-Subgroup =
    extensionality-type-subtype
      ( is-subgroup-subset-group-Prop G)
      ( is-subgroup-Subgroup G H)
      ( λ x → pair id id)
      ( extensionality-subtype (subset-Subgroup G H))
```

### Every subgroup induces two equivalence relations

#### The equivalence relation where `x ~ y` if and only if there exists `u : H` such that `xu = y`.

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Subgroup l2 G)
  where
  
  right-sim-Subgroup : (x y : type-Group G) → UU (l1 ⊔ l2)
  right-sim-Subgroup x y =
    fib (mul-Group G x ∘ inclusion-Subgroup G H) y

  is-prop-right-sim-Subgroup :
    (x y : type-Group G) → is-prop (right-sim-Subgroup x y)
  is-prop-right-sim-Subgroup x =
    is-prop-map-is-emb
      ( is-emb-comp'
        ( mul-Group G x)
        ( inclusion-Subgroup G H)
        ( is-emb-mul-Group G x)
        ( is-emb-inclusion-Subgroup G H))

  prop-right-eq-rel-Subgroup : (x y : type-Group G) → UU-Prop (l1 ⊔ l2)
  pr1 (prop-right-eq-rel-Subgroup x y) = right-sim-Subgroup x y
  pr2 (prop-right-eq-rel-Subgroup x y) =
    is-prop-right-sim-Subgroup x y

  refl-right-sim-Subgroup :
    is-reflexive-Rel-Prop prop-right-eq-rel-Subgroup
  pr1 (refl-right-sim-Subgroup {x}) = unit-Subgroup G H
  pr2 (refl-right-sim-Subgroup {x}) = right-unit-law-mul-Group G x

  symm-right-sim-Subgroup :
    is-symmetric-Rel-Prop prop-right-eq-rel-Subgroup
  pr1 (symm-right-sim-Subgroup {x} {y} (u , p)) =
    inv-Subgroup G H u
  pr2 (symm-right-sim-Subgroup {x} {y} (u , p)) =
    inv (transpose-eq-mul-Group G p)

  trans-right-sim-Subgroup :
    is-transitive-Rel-Prop prop-right-eq-rel-Subgroup
  pr1 (trans-right-sim-Subgroup {x} {y} {z} (u , p) (v , q)) =
    mul-Subgroup G H u v
  pr2 (trans-right-sim-Subgroup {x} {y} {z} (u , p) (v , q)) =
    ( inv
      ( associative-mul-Group G x
        ( inclusion-Subgroup G H u)
        ( inclusion-Subgroup G H v))) ∙
    ( ( ap (mul-Group' G (inclusion-Subgroup G H v)) p) ∙
      ( q))

  right-eq-rel-Subgroup : Eq-Rel (l1 ⊔ l2) (type-Group G)
  pr1 right-eq-rel-Subgroup = prop-right-eq-rel-Subgroup
  pr1 (pr2 right-eq-rel-Subgroup) = refl-right-sim-Subgroup
  pr1 (pr2 (pr2 right-eq-rel-Subgroup)) = symm-right-sim-Subgroup
  pr2 (pr2 (pr2 right-eq-rel-Subgroup)) = trans-right-sim-Subgroup
```

#### The equivalence relation where `x ~ y` if and only if there exists `u : H` such that `ux = y`.

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Subgroup l2 G)
  where
  
  left-sim-Subgroup : (x y : type-Group G) → UU (l1 ⊔ l2)
  left-sim-Subgroup x y =
    fib (mul-Group' G x ∘ inclusion-Subgroup G H) y

  is-prop-left-sim-Subgroup :
    (x y : type-Group G) → is-prop (left-sim-Subgroup x y)
  is-prop-left-sim-Subgroup x =
    is-prop-map-is-emb
      ( is-emb-comp'
        ( mul-Group' G x)
        ( inclusion-Subgroup G H)
        ( is-emb-mul-Group' G x)
        ( is-emb-inclusion-Subgroup G H))

  prop-left-eq-rel-Subgroup : (x y : type-Group G) → UU-Prop (l1 ⊔ l2)
  pr1 (prop-left-eq-rel-Subgroup x y) = left-sim-Subgroup x y
  pr2 (prop-left-eq-rel-Subgroup x y) =
    is-prop-left-sim-Subgroup x y

  refl-left-sim-Subgroup :
    is-reflexive-Rel-Prop prop-left-eq-rel-Subgroup
  pr1 (refl-left-sim-Subgroup {x}) = unit-Subgroup G H
  pr2 (refl-left-sim-Subgroup {x}) = left-unit-law-mul-Group G x

  symm-left-sim-Subgroup :
    is-symmetric-Rel-Prop prop-left-eq-rel-Subgroup
  pr1 (symm-left-sim-Subgroup {x} {y} (u , p)) =
    inv-Subgroup G H u
  pr2 (symm-left-sim-Subgroup {x} {y} (u , p)) =
    inv (transpose-eq-mul-Group' G p)

  trans-left-sim-Subgroup :
    is-transitive-Rel-Prop prop-left-eq-rel-Subgroup
  pr1 (trans-left-sim-Subgroup {x} {y} {z} (u , p) (v , q)) =
    mul-Subgroup G H v u
  pr2 (trans-left-sim-Subgroup {x} {y} {z} (u , p) (v , q)) =
    ( associative-mul-Group G
      ( inclusion-Subgroup G H v)
      ( inclusion-Subgroup G H u)
      ( x)) ∙
    ( ( ap (mul-Group G (inclusion-Subgroup G H v)) p) ∙
      ( q))

  left-eq-rel-Subgroup : Eq-Rel (l1 ⊔ l2) (type-Group G)
  pr1 left-eq-rel-Subgroup = prop-left-eq-rel-Subgroup
  pr1 (pr2 left-eq-rel-Subgroup) = refl-left-sim-Subgroup
  pr1 (pr2 (pr2 left-eq-rel-Subgroup)) = symm-left-sim-Subgroup
  pr2 (pr2 (pr2 left-eq-rel-Subgroup)) = trans-left-sim-Subgroup
```
