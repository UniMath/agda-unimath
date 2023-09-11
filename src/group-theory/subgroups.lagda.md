# Subgroups

```agda
module group-theory.subgroups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.integers
open import elementary-number-theory.natural-numbers

open import foundation.binary-relations
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalence-relations
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.large-binary-relations
open import foundation.powersets
open import foundation.propositions
open import foundation.sets
open import foundation.subtype-identity-principle
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.groups
open import group-theory.homomorphisms-groups
open import group-theory.integer-powers-of-elements-groups
open import group-theory.semigroups
open import group-theory.subsets-groups

open import order-theory.large-posets
open import order-theory.large-preorders
open import order-theory.order-preserving-maps-large-posets
open import order-theory.order-preserving-maps-large-preorders
open import order-theory.posets
open import order-theory.preorders
```

</details>

## Definitions

### Subgroups

```agda
module _
  {l1 l2 : Level} (G : Group l1) (P : subset-Group l2 G)
  where

  contains-unit-subset-group-Prop : Prop l2
  contains-unit-subset-group-Prop = P (unit-Group G)

  contains-unit-subset-Group : UU l2
  contains-unit-subset-Group =
    type-Prop contains-unit-subset-group-Prop

  is-prop-contains-unit-subset-Group :
    is-prop contains-unit-subset-Group
  is-prop-contains-unit-subset-Group =
    is-prop-type-Prop contains-unit-subset-group-Prop

  is-closed-under-multiplication-subset-group-Prop : Prop (l1 ⊔ l2)
  is-closed-under-multiplication-subset-group-Prop =
    Π-Prop
      ( type-Group G)
      ( λ x →
        Π-Prop
          ( type-Group G)
          ( λ y →
            hom-Prop (P x) (hom-Prop (P y) (P (mul-Group G x y)))))

  is-closed-under-multiplication-subset-Group : UU (l1 ⊔ l2)
  is-closed-under-multiplication-subset-Group =
    type-Prop is-closed-under-multiplication-subset-group-Prop

  is-prop-is-closed-under-multiplication-subset-Group :
    is-prop is-closed-under-multiplication-subset-Group
  is-prop-is-closed-under-multiplication-subset-Group =
    is-prop-type-Prop is-closed-under-multiplication-subset-group-Prop

  is-closed-under-inv-subset-group-Prop : Prop (l1 ⊔ l2)
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

  is-subgroup-subset-group-Prop : Prop (l1 ⊔ l2)
  is-subgroup-subset-group-Prop =
    prod-Prop
      ( contains-unit-subset-group-Prop)
      ( prod-Prop
        ( is-closed-under-multiplication-subset-group-Prop)
        ( is-closed-under-inv-subset-group-Prop))

  is-subgroup-subset-Group : UU (l1 ⊔ l2)
  is-subgroup-subset-Group = type-Prop is-subgroup-subset-group-Prop

  is-prop-is-subgroup-subset-Group : is-prop is-subgroup-subset-Group
  is-prop-is-subgroup-subset-Group =
    is-prop-type-Prop is-subgroup-subset-group-Prop
```

### The type of all subgroups of a group

```agda
Subgroup :
  (l : Level) {l1 : Level} (G : Group l1) → UU ((lsuc l) ⊔ l1)
Subgroup l G = type-subtype (is-subgroup-subset-group-Prop {l2 = l} G)

module _
  {l1 l2 : Level} (G : Group l1) (H : Subgroup l2 G)
  where

  subset-Subgroup : subset-Group l2 G
  subset-Subgroup =
    inclusion-subtype (is-subgroup-subset-group-Prop G) H

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

  is-closed-under-eq-Subgroup :
    {x y : type-Group G} →
    is-in-Subgroup x → (x ＝ y) → is-in-Subgroup y
  is-closed-under-eq-Subgroup =
    is-closed-under-eq-subtype subset-Subgroup

  is-closed-under-eq-Subgroup' :
    {x y : type-Group G} →
    is-in-Subgroup y → (x ＝ y) → is-in-Subgroup x
  is-closed-under-eq-Subgroup' =
    is-closed-under-eq-subtype' subset-Subgroup

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

  is-closed-under-multiplication-Subgroup :
    is-closed-under-multiplication-subset-Group G subset-Subgroup
  is-closed-under-multiplication-Subgroup = pr1 (pr2 is-subgroup-Subgroup)

  is-closed-under-inv-Subgroup :
    is-closed-under-inv-subset-Group G subset-Subgroup
  is-closed-under-inv-Subgroup = pr2 (pr2 is-subgroup-Subgroup)

  is-closed-under-inv-Subgroup' :
    (x : type-Group G) →
    is-in-Subgroup (inv-Group G x) → is-in-Subgroup x
  is-closed-under-inv-Subgroup' x p =
    is-closed-under-eq-Subgroup
      ( is-closed-under-inv-Subgroup (inv-Group G x) p)
      ( inv-inv-Group G x)

  is-in-subgroup-left-factor-Subgroup :
    (x y : type-Group G) →
    is-in-Subgroup (mul-Group G x y) → is-in-Subgroup y →
    is-in-Subgroup x
  is-in-subgroup-left-factor-Subgroup x y p q =
    is-closed-under-eq-Subgroup
      ( is-closed-under-multiplication-Subgroup
        ( mul-Group G x y)
        ( inv-Group G y)
        ( p)
        ( is-closed-under-inv-Subgroup y q))
      ( is-retraction-right-div-Group G y x)

  is-in-subgroup-right-factor-Subgroup :
    (x y : type-Group G) →
    is-in-Subgroup (mul-Group G x y) → is-in-Subgroup x →
    is-in-Subgroup y
  is-in-subgroup-right-factor-Subgroup x y p q =
    is-closed-under-eq-Subgroup
      ( is-closed-under-multiplication-Subgroup
        ( inv-Group G x)
        ( mul-Group G x y)
        ( is-closed-under-inv-Subgroup x q)
        ( p))
      ( is-retraction-left-div-Group G x y)

  is-closed-under-powers-int-Subgroup :
    (k : ℤ) (x : type-Group G) →
    is-in-Subgroup x → is-in-Subgroup (integer-power-Group G k x)
  is-closed-under-powers-int-Subgroup (inl zero-ℕ) x H =
    is-closed-under-eq-Subgroup'
      ( is-closed-under-inv-Subgroup x H)
      ( right-unit-law-mul-Group G (inv-Group G x))
  is-closed-under-powers-int-Subgroup (inl (succ-ℕ k)) x H =
    is-closed-under-multiplication-Subgroup
      ( inv-Group G x)
      ( integer-power-Group G (inl k) x)
      ( is-closed-under-inv-Subgroup x H)
      ( is-closed-under-powers-int-Subgroup (inl k) x H)
  is-closed-under-powers-int-Subgroup (inr (inl star)) x H =
    contains-unit-Subgroup
  is-closed-under-powers-int-Subgroup (inr (inr zero-ℕ)) x H =
    is-closed-under-eq-Subgroup' H (right-unit-law-mul-Group G x)
  is-closed-under-powers-int-Subgroup (inr (inr (succ-ℕ k))) x H =
    is-closed-under-multiplication-Subgroup
      ( x)
      ( integer-power-Group G (inr (inr k)) x)
      ( H)
      ( is-closed-under-powers-int-Subgroup (inr (inr k)) x H)

is-emb-subset-Subgroup :
  {l1 l2 : Level} (G : Group l1) →
  is-emb (subset-Subgroup {l2 = l2} G)
is-emb-subset-Subgroup G =
  is-emb-inclusion-subtype (is-subgroup-subset-group-Prop G)
```

### The underlying group of a subgroup

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Subgroup l2 G)
  where

  type-group-Subgroup : UU (l1 ⊔ l2)
  type-group-Subgroup = type-subtype (subset-Subgroup G H)

  map-inclusion-Subgroup : type-group-Subgroup → type-Group G
  map-inclusion-Subgroup =
    inclusion-subtype (subset-Subgroup G H)

  eq-subgroup-eq-group : is-injective map-inclusion-Subgroup
  eq-subgroup-eq-group {x} {y} =
    map-inv-is-equiv (is-emb-inclusion-Subgroup G H x y)

  set-group-Subgroup : Set (l1 ⊔ l2)
  pr1 set-group-Subgroup = type-group-Subgroup
  pr2 set-group-Subgroup =
    is-set-type-subtype (subset-Subgroup G H) (is-set-type-Group G)

  mul-Subgroup : (x y : type-group-Subgroup) → type-group-Subgroup
  pr1 (mul-Subgroup x y) = mul-Group G (pr1 x) (pr1 y)
  pr2 (mul-Subgroup x y) =
    is-closed-under-multiplication-Subgroup G H (pr1 x) (pr1 y) (pr2 x) (pr2 y)

  associative-mul-Subgroup :
    (x y z : type-group-Subgroup) →
    Id
      ( mul-Subgroup (mul-Subgroup x y) z)
      ( mul-Subgroup x (mul-Subgroup y z))
  associative-mul-Subgroup x y z =
    eq-subgroup-eq-group
      ( associative-mul-Group G (pr1 x) (pr1 y) (pr1 z))

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
  pr2 (inv-Subgroup x) =
    is-closed-under-inv-Subgroup G H (pr1 x) (pr2 x)

  left-inverse-law-mul-Subgroup :
    ( x : type-group-Subgroup) →
    Id
      ( mul-Subgroup (inv-Subgroup x) x)
      ( unit-Subgroup)
  left-inverse-law-mul-Subgroup x =
    eq-subgroup-eq-group (left-inverse-law-mul-Group G (pr1 x))

  right-inverse-law-mul-Subgroup :
    (x : type-group-Subgroup) →
    Id
      ( mul-Subgroup x (inv-Subgroup x))
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
  pr2 (pr2 (pr2 (pr2 group-Subgroup))) =
    right-inverse-law-mul-Subgroup
```

### The inclusion of the underlying group of a subgroup into the ambient group

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Subgroup l2 G)
  where

  preserves-mul-inclusion-Subgroup :
    preserves-mul-Group
      ( group-Subgroup G H)
      ( G)
      ( map-inclusion-Subgroup G H)
  preserves-mul-inclusion-Subgroup x y = refl

  preserves-unit-inclusion-Subgroup :
    preserves-unit-Group
      ( group-Subgroup G H)
      ( G)
      ( map-inclusion-Subgroup G H)
  preserves-unit-inclusion-Subgroup = refl

  preserves-inverses-inclusion-Subgroup :
    preserves-inverses-Group
      ( group-Subgroup G H)
      ( G)
      ( map-inclusion-Subgroup G H)
  preserves-inverses-inclusion-Subgroup x = refl

  hom-inclusion-Subgroup :
    type-hom-Group (group-Subgroup G H) G
  pr1 hom-inclusion-Subgroup = inclusion-Subgroup G H
  pr2 hom-inclusion-Subgroup = preserves-mul-inclusion-Subgroup
```

## Properties

### Extensionality of the type of all subgroups

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Subgroup l2 G)
  where

  has-same-elements-Subgroup :
    {l3 : Level} → Subgroup l3 G → UU (l1 ⊔ l2 ⊔ l3)
  has-same-elements-Subgroup K =
    has-same-elements-subtype
      ( subset-Subgroup G H)
      ( subset-Subgroup G K)

  extensionality-Subgroup :
    (K : Subgroup l2 G) → (H ＝ K) ≃ has-same-elements-Subgroup K
  extensionality-Subgroup =
    extensionality-type-subtype
      ( is-subgroup-subset-group-Prop G)
      ( is-subgroup-Subgroup G H)
      ( λ x → pair id id)
      ( extensionality-subtype (subset-Subgroup G H))

  refl-has-same-elements-Subgroup : has-same-elements-Subgroup H
  refl-has-same-elements-Subgroup =
    refl-has-same-elements-subtype (subset-Subgroup G H)

  has-same-elements-eq-Subgroup :
    (K : Subgroup l2 G) → (H ＝ K) → has-same-elements-Subgroup K
  has-same-elements-eq-Subgroup K =
    map-equiv (extensionality-Subgroup K)

  eq-has-same-elements-Subgroup :
    (K : Subgroup l2 G) → has-same-elements-Subgroup K → (H ＝ K)
  eq-has-same-elements-Subgroup K =
    map-inv-equiv (extensionality-Subgroup K)
```

### The containment relation of subgroups

```agda
leq-Subgroup-Prop :
  {l1 l2 l3 : Level} (G : Group l1) →
  Subgroup l2 G → Subgroup l3 G → Prop (l1 ⊔ l2 ⊔ l3)
leq-Subgroup-Prop G H K =
  leq-subtype-Prop
    ( subset-Subgroup G H)
    ( subset-Subgroup G K)

leq-Subgroup :
  {l1 l2 l3 : Level} (G : Group l1) →
  Subgroup l2 G → Subgroup l3 G → UU (l1 ⊔ l2 ⊔ l3)
leq-Subgroup G H K = subset-Subgroup G H ⊆ subset-Subgroup G K

refl-leq-Subgroup :
  {l1 : Level} (G : Group l1) →
  is-large-reflexive (λ l → Subgroup l G) (leq-Subgroup G)
refl-leq-Subgroup G H = refl-leq-subtype (subset-Subgroup G H)

transitive-leq-Subgroup :
  {l1 : Level} (G : Group l1) →
  is-large-transitive (λ l → Subgroup l G) (leq-Subgroup G)
transitive-leq-Subgroup G H K L =
  transitive-leq-subtype
    ( subset-Subgroup G H)
    ( subset-Subgroup G K)
    ( subset-Subgroup G L)

antisymmetric-leq-Subgroup :
  {l1 : Level} (G : Group l1) →
  is-large-antisymmetric (λ l → Subgroup l G) (leq-Subgroup G)
antisymmetric-leq-Subgroup G H K α β =
  eq-has-same-elements-Subgroup G H K (λ x → (α x , β x))

Subgroup-Large-Preorder :
  {l1 : Level} (G : Group l1) →
  Large-Preorder (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
type-Large-Preorder (Subgroup-Large-Preorder G) l2 = Subgroup l2 G
leq-Large-Preorder-Prop (Subgroup-Large-Preorder G) H K =
  leq-Subgroup-Prop G H K
refl-leq-Large-Preorder (Subgroup-Large-Preorder G) =
  refl-leq-Subgroup G
transitive-leq-Large-Preorder (Subgroup-Large-Preorder G) =
  transitive-leq-Subgroup G

Subgroup-Preorder :
  {l1 : Level} (l2 : Level) (G : Group l1) →
  Preorder (l1 ⊔ lsuc l2) (l1 ⊔ l2)
Subgroup-Preorder l2 G =
  preorder-Large-Preorder (Subgroup-Large-Preorder G) l2

Subgroup-Large-Poset :
  {l1 : Level} (G : Group l1) →
  Large-Poset (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
large-preorder-Large-Poset (Subgroup-Large-Poset G) =
  Subgroup-Large-Preorder G
antisymmetric-leq-Large-Poset (Subgroup-Large-Poset G) =
  antisymmetric-leq-Subgroup G

Subgroup-Poset :
  {l1 : Level} (l2 : Level) (G : Group l1) →
  Poset (l1 ⊔ lsuc l2) (l1 ⊔ l2)
Subgroup-Poset l2 G = poset-Large-Poset (Subgroup-Large-Poset G) l2

preserves-order-subset-Subgroup :
  {l1 l2 l3 : Level} (G : Group l1) (H : Subgroup l2 G) (K : Subgroup l3 G) →
  leq-Subgroup G H K → (subset-Subgroup G H ⊆ subset-Subgroup G K)
preserves-order-subset-Subgroup G H K = id

subset-subgroup-hom-large-poset-Group :
  {l1 : Level} (G : Group l1) →
  hom-Large-Poset
    ( id)
    ( Subgroup-Large-Poset G)
    ( powerset-Large-Poset (type-Group G))
map-hom-Large-Preorder
  ( subset-subgroup-hom-large-poset-Group G) =
  subset-Subgroup G
preserves-order-hom-Large-Preorder
  ( subset-subgroup-hom-large-poset-Group G) =
  preserves-order-subset-Subgroup G
```

### Every subgroup induces two equivalence relations

#### The equivalence relation where `x ~ y` if and only if `x⁻¹ y ∈ H`

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Subgroup l2 G)
  where

  right-sim-Subgroup : (x y : type-Group G) → UU l2
  right-sim-Subgroup x y = is-in-Subgroup G H (left-div-Group G x y)

  is-prop-right-sim-Subgroup :
    (x y : type-Group G) → is-prop (right-sim-Subgroup x y)
  is-prop-right-sim-Subgroup x y =
    is-prop-is-in-Subgroup G H (left-div-Group G x y)

  prop-right-eq-rel-Subgroup : (x y : type-Group G) → Prop l2
  pr1 (prop-right-eq-rel-Subgroup x y) = right-sim-Subgroup x y
  pr2 (prop-right-eq-rel-Subgroup x y) =
    is-prop-right-sim-Subgroup x y

  refl-right-sim-Subgroup : is-reflexive right-sim-Subgroup
  refl-right-sim-Subgroup x =
    tr
      ( is-in-Subgroup G H)
      ( inv (left-inverse-law-mul-Group G x))
      ( contains-unit-Subgroup G H)

  symmetric-right-sim-Subgroup : is-symmetric right-sim-Subgroup
  symmetric-right-sim-Subgroup x y p =
    tr
      ( is-in-Subgroup G H)
      ( inv-left-div-Group G x y)
      ( is-closed-under-inv-Subgroup G H
        ( left-div-Group G x y)
        ( p))

  transitive-right-sim-Subgroup : is-transitive right-sim-Subgroup
  transitive-right-sim-Subgroup x y z p q =
    tr
      ( is-in-Subgroup G H)
      ( mul-left-div-Group G x y z)
      ( is-closed-under-multiplication-Subgroup G H
        ( left-div-Group G x y)
        ( left-div-Group G y z)
        ( q)
        ( p))

  right-eq-rel-Subgroup : Equivalence-Relation l2 (type-Group G)
  pr1 right-eq-rel-Subgroup = prop-right-eq-rel-Subgroup
  pr1 (pr2 right-eq-rel-Subgroup) = refl-right-sim-Subgroup
  pr1 (pr2 (pr2 right-eq-rel-Subgroup)) = symmetric-right-sim-Subgroup
  pr2 (pr2 (pr2 right-eq-rel-Subgroup)) = transitive-right-sim-Subgroup
```

#### The equivalence relation where `x ~ y` if and only if `xy⁻¹ ∈ H`

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Subgroup l2 G)
  where

  left-sim-Subgroup : (x y : type-Group G) → UU l2
  left-sim-Subgroup x y = is-in-Subgroup G H (right-div-Group G x y)

  is-prop-left-sim-Subgroup :
    (x y : type-Group G) → is-prop (left-sim-Subgroup x y)
  is-prop-left-sim-Subgroup x y =
    is-prop-is-in-Subgroup G H (right-div-Group G x y)

  prop-left-eq-rel-Subgroup : (x y : type-Group G) → Prop l2
  pr1 (prop-left-eq-rel-Subgroup x y) = left-sim-Subgroup x y
  pr2 (prop-left-eq-rel-Subgroup x y) =
    is-prop-left-sim-Subgroup x y

  refl-left-sim-Subgroup : is-reflexive left-sim-Subgroup
  refl-left-sim-Subgroup x =
    tr
      ( is-in-Subgroup G H)
      ( inv (right-inverse-law-mul-Group G x))
      ( contains-unit-Subgroup G H)

  symmetric-left-sim-Subgroup : is-symmetric left-sim-Subgroup
  symmetric-left-sim-Subgroup x y p =
    tr
      ( is-in-Subgroup G H)
      ( inv-right-div-Group G x y)
      ( is-closed-under-inv-Subgroup G H
        ( right-div-Group G x y)
        ( p))

  transitive-left-sim-Subgroup : is-transitive left-sim-Subgroup
  transitive-left-sim-Subgroup x y z p q =
    tr
      ( is-in-Subgroup G H)
      ( mul-right-div-Group G x y z)
      ( is-closed-under-multiplication-Subgroup G H
        ( right-div-Group G x y)
        ( right-div-Group G y z)
        ( q)
        ( p))

  left-eq-rel-Subgroup : Equivalence-Relation l2 (type-Group G)
  pr1 left-eq-rel-Subgroup = prop-left-eq-rel-Subgroup
  pr1 (pr2 left-eq-rel-Subgroup) = refl-left-sim-Subgroup
  pr1 (pr2 (pr2 left-eq-rel-Subgroup)) = symmetric-left-sim-Subgroup
  pr2 (pr2 (pr2 left-eq-rel-Subgroup)) = transitive-left-sim-Subgroup
```
