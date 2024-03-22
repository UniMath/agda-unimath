# Normal subgroups

```agda
module group-theory.normal-subgroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalence-relations
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.large-binary-relations
open import foundation.large-reflexive-relations
open import foundation.large-transitive-binary-relations
open import foundation.propositions
open import foundation.reflexive-relations
open import foundation.subtype-identity-principle
open import foundation.subtypes
open import foundation.transitive-binary-relations
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.congruence-relations-groups
open import group-theory.conjugation
open import group-theory.groups
open import group-theory.subgroups
open import group-theory.subsets-groups

open import order-theory.large-posets
open import order-theory.large-preorders
open import order-theory.order-preserving-maps-large-posets
open import order-theory.order-preserving-maps-large-preorders
open import order-theory.posets
open import order-theory.preorders
```

</details>

## Idea

A normal subgroup of `G` is a subgroup `H` of `G` which is closed under
conjugation.

## Definition

```agda
is-normal-prop-Subgroup :
  {l1 l2 : Level} (G : Group l1) (H : Subgroup l2 G) → Prop (l1 ⊔ l2)
is-normal-prop-Subgroup G H =
  Π-Prop
    ( type-Group G)
    ( λ g →
      Π-Prop
        ( type-Subgroup G H)
        ( λ h →
          subset-Subgroup G H
            ( conjugation-Group G g (inclusion-Subgroup G H h))))

is-normal-Subgroup :
  {l1 l2 : Level} (G : Group l1) (H : Subgroup l2 G) → UU (l1 ⊔ l2)
is-normal-Subgroup G H = type-Prop (is-normal-prop-Subgroup G H)

is-prop-is-normal-Subgroup :
  {l1 l2 : Level} (G : Group l1) (H : Subgroup l2 G) →
  is-prop (is-normal-Subgroup G H)
is-prop-is-normal-Subgroup G H =
  is-prop-type-Prop (is-normal-prop-Subgroup G H)

is-normal-Subgroup' :
  {l1 l2 : Level} (G : Group l1) (H : Subgroup l2 G) → UU (l1 ⊔ l2)
is-normal-Subgroup' G H =
  (x : type-Group G) (y : type-Subgroup G H) →
  is-in-Subgroup G H
    ( conjugation-Group' G x (inclusion-Subgroup G H y))

is-normal-is-normal-Subgroup :
  {l1 l2 : Level} (G : Group l1) (H : Subgroup l2 G) →
  is-normal-Subgroup G H → is-normal-Subgroup' G H
is-normal-is-normal-Subgroup G H K x y =
  tr
    ( is-in-Subgroup G H)
    ( inv (htpy-conjugation-Group G x (inclusion-Subgroup G H y)))
    ( K (inv-Group G x) y)

is-normal-is-normal-Subgroup' :
  {l1 l2 : Level} (G : Group l1) (H : Subgroup l2 G) →
  is-normal-Subgroup' G H → is-normal-Subgroup G H
is-normal-is-normal-Subgroup' G H K x y =
  tr
    ( is-in-Subgroup G H)
    ( inv (htpy-conjugation-Group' G x (inclusion-Subgroup G H y)))
    ( K (inv-Group G x) y)

Normal-Subgroup :
  {l1 : Level} (l2 : Level) (G : Group l1) → UU (l1 ⊔ lsuc l2)
Normal-Subgroup l2 G = Σ (Subgroup l2 G) (is-normal-Subgroup G)

module _
  {l1 l2 : Level} (G : Group l1) (N : Normal-Subgroup l2 G)
  where

  subgroup-Normal-Subgroup : Subgroup l2 G
  subgroup-Normal-Subgroup = pr1 N

  subset-Normal-Subgroup : subset-Group l2 G
  subset-Normal-Subgroup = subset-Subgroup G subgroup-Normal-Subgroup

  type-Normal-Subgroup : UU (l1 ⊔ l2)
  type-Normal-Subgroup = type-Subgroup G subgroup-Normal-Subgroup

  inclusion-Normal-Subgroup : type-Normal-Subgroup → type-Group G
  inclusion-Normal-Subgroup =
    inclusion-Subgroup G subgroup-Normal-Subgroup

  is-emb-inclusion-Normal-Subgroup : is-emb inclusion-Normal-Subgroup
  is-emb-inclusion-Normal-Subgroup =
    is-emb-inclusion-Subgroup G subgroup-Normal-Subgroup

  emb-inclusion-Normal-Subgroup : type-Normal-Subgroup ↪ type-Group G
  emb-inclusion-Normal-Subgroup =
    emb-inclusion-Subgroup G subgroup-Normal-Subgroup

  is-in-Normal-Subgroup : type-Group G → UU l2
  is-in-Normal-Subgroup = is-in-Subgroup G subgroup-Normal-Subgroup

  is-closed-under-eq-Normal-Subgroup :
    {x y : type-Group G} →
    is-in-Normal-Subgroup x → (x ＝ y) → is-in-Normal-Subgroup y
  is-closed-under-eq-Normal-Subgroup =
    is-closed-under-eq-subtype subset-Normal-Subgroup

  is-closed-under-eq-Normal-Subgroup' :
    {x y : type-Group G} →
    is-in-Normal-Subgroup y → (x ＝ y) → is-in-Normal-Subgroup x
  is-closed-under-eq-Normal-Subgroup' =
    is-closed-under-eq-subtype' subset-Normal-Subgroup

  is-prop-is-in-Normal-Subgroup :
    (g : type-Group G) → is-prop (is-in-Normal-Subgroup g)
  is-prop-is-in-Normal-Subgroup =
    is-prop-is-in-Subgroup G subgroup-Normal-Subgroup

  is-in-normal-subgroup-inclusion-Normal-Subgroup :
    (x : type-Normal-Subgroup) →
    is-in-Normal-Subgroup (inclusion-Normal-Subgroup x)
  is-in-normal-subgroup-inclusion-Normal-Subgroup =
    is-in-subgroup-inclusion-Subgroup G subgroup-Normal-Subgroup

  is-subgroup-Normal-Subgroup :
    is-subgroup-subset-Group G subset-Normal-Subgroup
  is-subgroup-Normal-Subgroup =
    is-subgroup-Subgroup G subgroup-Normal-Subgroup

  contains-unit-Normal-Subgroup : is-in-Normal-Subgroup (unit-Group G)
  contains-unit-Normal-Subgroup =
    contains-unit-Subgroup G subgroup-Normal-Subgroup

  unit-Normal-Subgroup : type-Normal-Subgroup
  unit-Normal-Subgroup = unit-Subgroup G subgroup-Normal-Subgroup

  is-closed-under-multiplication-Normal-Subgroup :
    is-closed-under-multiplication-subset-Group G subset-Normal-Subgroup
  is-closed-under-multiplication-Normal-Subgroup =
    is-closed-under-multiplication-Subgroup G subgroup-Normal-Subgroup

  mul-Normal-Subgroup :
    type-Normal-Subgroup → type-Normal-Subgroup → type-Normal-Subgroup
  mul-Normal-Subgroup = mul-Subgroup G subgroup-Normal-Subgroup

  is-closed-under-inverses-Normal-Subgroup :
    is-closed-under-inverses-subset-Group G subset-Normal-Subgroup
  is-closed-under-inverses-Normal-Subgroup =
    is-closed-under-inverses-Subgroup G subgroup-Normal-Subgroup

  inv-Normal-Subgroup : type-Normal-Subgroup → type-Normal-Subgroup
  inv-Normal-Subgroup = inv-Subgroup G subgroup-Normal-Subgroup

  is-closed-under-inverses-Normal-Subgroup' :
    (x : type-Group G) →
    is-in-Normal-Subgroup (inv-Group G x) → is-in-Normal-Subgroup x
  is-closed-under-inverses-Normal-Subgroup' =
    is-closed-under-inverses-Subgroup' G subgroup-Normal-Subgroup

  is-in-normal-subgroup-left-factor-Normal-Subgroup :
    (x y : type-Group G) →
    is-in-Normal-Subgroup (mul-Group G x y) →
    is-in-Normal-Subgroup y → is-in-Normal-Subgroup x
  is-in-normal-subgroup-left-factor-Normal-Subgroup =
    is-in-subgroup-left-factor-Subgroup G subgroup-Normal-Subgroup

  is-in-normal-subgroup-right-factor-Normal-Subgroup :
    (x y : type-Group G) →
    is-in-Normal-Subgroup (mul-Group G x y) →
    is-in-Normal-Subgroup x → is-in-Normal-Subgroup y
  is-in-normal-subgroup-right-factor-Normal-Subgroup =
    is-in-subgroup-right-factor-Subgroup G subgroup-Normal-Subgroup

  group-Normal-Subgroup : Group (l1 ⊔ l2)
  group-Normal-Subgroup = group-Subgroup G subgroup-Normal-Subgroup

  is-normal-Normal-Subgroup :
    (x y : type-Group G) → is-in-Normal-Subgroup y →
    is-in-Normal-Subgroup (conjugation-Group G x y)
  is-normal-Normal-Subgroup x y p = pr2 N x (y , p)

  is-normal-Normal-Subgroup' :
    (x y : type-Group G) → is-in-Normal-Subgroup y →
    is-in-Normal-Subgroup (conjugation-Group' G x y)
  is-normal-Normal-Subgroup' x y p =
    is-normal-is-normal-Subgroup G
      ( subgroup-Normal-Subgroup)
      ( λ x y → is-normal-Normal-Subgroup x (pr1 y) (pr2 y))
      ( x)
      ( pair y p)

  closure-property-Normal-Subgroup :
    {x y z : type-Group G} →
    is-in-Normal-Subgroup y →
    is-in-Normal-Subgroup (mul-Group G x z) →
    is-in-Normal-Subgroup (mul-Group G (mul-Group G x y) z)
  closure-property-Normal-Subgroup {x} {y} {z} p q =
    is-closed-under-eq-Normal-Subgroup
      ( is-closed-under-multiplication-Normal-Subgroup
        ( is-normal-Normal-Subgroup x y p)
        ( q))
      ( ( associative-mul-Group G
          ( mul-Group G x y)
          ( inv-Group G x)
          ( mul-Group G x z)) ∙
        ( ap
          ( mul-Group G (mul-Group G x y))
          ( is-retraction-left-div-Group G x z)))

  closure-property-Normal-Subgroup' :
    {x y z : type-Group G} →
    is-in-Normal-Subgroup y →
    is-in-Normal-Subgroup (mul-Group G x z) →
    is-in-Normal-Subgroup (mul-Group G x (mul-Group G y z))
  closure-property-Normal-Subgroup' {x} {y} {z} p q =
    is-closed-under-eq-Normal-Subgroup
      ( closure-property-Normal-Subgroup p q)
      ( associative-mul-Group G x y z)

  conjugation-Normal-Subgroup :
    type-Group G → type-Normal-Subgroup → type-Normal-Subgroup
  pr1 (conjugation-Normal-Subgroup y u) =
    conjugation-Group G y (inclusion-Normal-Subgroup u)
  pr2 (conjugation-Normal-Subgroup y u) =
    is-normal-Normal-Subgroup y (pr1 u) (pr2 u)

  conjugation-Normal-Subgroup' :
    type-Group G → type-Normal-Subgroup → type-Normal-Subgroup
  pr1 (conjugation-Normal-Subgroup' y u) =
    conjugation-Group' G y (inclusion-Normal-Subgroup u)
  pr2 (conjugation-Normal-Subgroup' y u) =
    is-normal-Normal-Subgroup' y (pr1 u) (pr2 u)
```

## Properties

### Extensionality of the type of all normal subgroups

```agda
module _
  {l1 l2 : Level} (G : Group l1) (N : Normal-Subgroup l2 G)
  where

  has-same-elements-Normal-Subgroup :
    {l3 : Level} → Normal-Subgroup l3 G → UU (l1 ⊔ l2 ⊔ l3)
  has-same-elements-Normal-Subgroup K =
    has-same-elements-Subgroup G
      ( subgroup-Normal-Subgroup G N)
      ( subgroup-Normal-Subgroup G K)

  extensionality-Normal-Subgroup :
    (K : Normal-Subgroup l2 G) →
    (N ＝ K) ≃ has-same-elements-Normal-Subgroup K
  extensionality-Normal-Subgroup =
    extensionality-type-subtype
      ( is-normal-prop-Subgroup G)
      ( λ x y →
        is-normal-Normal-Subgroup G N x (pr1 y) (pr2 y))
      ( λ x → pair id id)
      ( extensionality-Subgroup G (subgroup-Normal-Subgroup G N))

  eq-has-same-elements-Normal-Subgroup :
    (K : Normal-Subgroup l2 G) →
    has-same-elements-Normal-Subgroup K → N ＝ K
  eq-has-same-elements-Normal-Subgroup K =
    map-inv-equiv (extensionality-Normal-Subgroup K)
```

### The containment relation of normal subgroups

```agda
leq-prop-Normal-Subgroup :
  {l1 l2 l3 : Level} (G : Group l1) →
  Normal-Subgroup l2 G → Normal-Subgroup l3 G → Prop (l1 ⊔ l2 ⊔ l3)
leq-prop-Normal-Subgroup G H K =
  leq-prop-Subgroup G
    ( subgroup-Normal-Subgroup G H)
    ( subgroup-Normal-Subgroup G K)

leq-Normal-Subgroup :
  {l1 l2 l3 : Level} (G : Group l1) →
  Normal-Subgroup l2 G → Normal-Subgroup l3 G → UU (l1 ⊔ l2 ⊔ l3)
leq-Normal-Subgroup G H K =
  leq-Subgroup G
    ( subgroup-Normal-Subgroup G H)
    ( subgroup-Normal-Subgroup G K)

is-prop-leq-Normal-Subgroup :
  {l1 l2 l3 : Level} (G : Group l1) →
  (N : Normal-Subgroup l2 G) (M : Normal-Subgroup l3 G) →
  is-prop (leq-Normal-Subgroup G N M)
is-prop-leq-Normal-Subgroup G N M =
  is-prop-leq-Subgroup G
    ( subgroup-Normal-Subgroup G N)
    ( subgroup-Normal-Subgroup G M)

refl-leq-Normal-Subgroup :
  {l1 : Level} (G : Group l1) →
  is-reflexive-Large-Relation
    ( λ l → Normal-Subgroup l G)
    ( leq-Normal-Subgroup G)
refl-leq-Normal-Subgroup G H =
  refl-leq-Subgroup G (subgroup-Normal-Subgroup G H)

transitive-leq-Normal-Subgroup :
  {l1 : Level} (G : Group l1) →
  is-transitive-Large-Relation
    ( λ l → Normal-Subgroup l G)
    ( leq-Normal-Subgroup G)
transitive-leq-Normal-Subgroup G H K L =
  transitive-leq-Subgroup G
    ( subgroup-Normal-Subgroup G H)
    ( subgroup-Normal-Subgroup G K)
    ( subgroup-Normal-Subgroup G L)

antisymmetric-leq-Normal-Subgroup :
  {l1 : Level} (G : Group l1) →
  is-antisymmetric-Large-Relation
    ( λ l → Normal-Subgroup l G)
    ( leq-Normal-Subgroup G)
antisymmetric-leq-Normal-Subgroup G H K α β =
  eq-has-same-elements-Normal-Subgroup G H K (λ x → (α x , β x))

Normal-Subgroup-Large-Preorder :
  {l1 : Level} (G : Group l1) →
  Large-Preorder (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
type-Large-Preorder (Normal-Subgroup-Large-Preorder G) l2 =
  Normal-Subgroup l2 G
leq-prop-Large-Preorder (Normal-Subgroup-Large-Preorder G) H K =
  leq-prop-Normal-Subgroup G H K
refl-leq-Large-Preorder (Normal-Subgroup-Large-Preorder G) =
  refl-leq-Normal-Subgroup G
transitive-leq-Large-Preorder (Normal-Subgroup-Large-Preorder G) =
  transitive-leq-Normal-Subgroup G

Normal-Subgroup-Preorder :
  {l1 : Level} (l2 : Level) (G : Group l1) →
  Preorder (l1 ⊔ lsuc l2) (l1 ⊔ l2)
Normal-Subgroup-Preorder l2 G =
  preorder-Large-Preorder (Normal-Subgroup-Large-Preorder G) l2

Normal-Subgroup-Large-Poset :
  {l1 : Level} (G : Group l1) →
  Large-Poset (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
large-preorder-Large-Poset (Normal-Subgroup-Large-Poset G) =
  Normal-Subgroup-Large-Preorder G
antisymmetric-leq-Large-Poset (Normal-Subgroup-Large-Poset G) =
  antisymmetric-leq-Normal-Subgroup G

Normal-Subgroup-Poset :
  {l1 : Level} (l2 : Level) (G : Group l1) →
  Poset (l1 ⊔ lsuc l2) (l1 ⊔ l2)
Normal-Subgroup-Poset l2 G =
  poset-Large-Poset (Normal-Subgroup-Large-Poset G) l2

preserves-order-subgroup-Normal-Subgroup :
  {l1 l2 l3 : Level} (G : Group l1)
  (N : Normal-Subgroup l2 G) (M : Normal-Subgroup l3 G) →
  leq-Normal-Subgroup G N M →
  leq-Subgroup G (subgroup-Normal-Subgroup G N) (subgroup-Normal-Subgroup G M)
preserves-order-subgroup-Normal-Subgroup G N M = id

subgroup-normal-subgroup-hom-Large-Poset :
  {l1 : Level} (G : Group l1) →
  hom-Large-Poset
    ( λ l → l)
    ( Normal-Subgroup-Large-Poset G)
    ( Subgroup-Large-Poset G)
subgroup-normal-subgroup-hom-Large-Poset G =
  make-hom-Large-Preorder
    ( subgroup-Normal-Subgroup G)
    ( preserves-order-subgroup-Normal-Subgroup G)
```

### Normal subgroups are in 1-1 correspondence with congruence relations on groups

#### The standard similarity relation obtained from a normal subgroup

```agda
module _
  {l1 l2 : Level} (G : Group l1) (N : Normal-Subgroup l2 G)
  where

  sim-congruence-Normal-Subgroup : (x y : type-Group G) → UU l2
  sim-congruence-Normal-Subgroup =
    right-sim-Subgroup G (subgroup-Normal-Subgroup G N)

  is-prop-sim-congruence-Normal-Subgroup :
    (x y : type-Group G) →
    is-prop (sim-congruence-Normal-Subgroup x y)
  is-prop-sim-congruence-Normal-Subgroup =
    is-prop-right-sim-Subgroup G (subgroup-Normal-Subgroup G N)

  prop-congruence-Normal-Subgroup :
    (x y : type-Group G) → Prop l2
  prop-congruence-Normal-Subgroup =
    prop-right-equivalence-relation-Subgroup G (subgroup-Normal-Subgroup G N)
```

#### The left equivalence relation obtained from a normal subgroup

```agda
  left-equivalence-relation-congruence-Normal-Subgroup :
    equivalence-relation l2 (type-Group G)
  left-equivalence-relation-congruence-Normal-Subgroup =
    left-equivalence-relation-Subgroup G (subgroup-Normal-Subgroup G N)

  left-sim-congruence-Normal-Subgroup :
    type-Group G → type-Group G → UU l2
  left-sim-congruence-Normal-Subgroup =
    left-sim-Subgroup G (subgroup-Normal-Subgroup G N)
```

#### The left similarity relation of a normal subgroup relates the same elements as the standard similarity relation

```agda
  left-sim-sim-congruence-Normal-Subgroup :
    (x y : type-Group G) →
    sim-congruence-Normal-Subgroup x y →
    left-sim-congruence-Normal-Subgroup x y
  left-sim-sim-congruence-Normal-Subgroup x y H =
    is-closed-under-eq-Normal-Subgroup G N
      ( is-normal-Normal-Subgroup G N y
        ( inv-Group G (left-div-Group G x y))
        ( is-closed-under-inverses-Normal-Subgroup G N H))
      ( ( ap (conjugation-Group G y) (inv-left-div-Group G x y)) ∙
        ( conjugation-left-div-Group G y x))

  sim-left-sim-congruence-Normal-Subgroup :
    (x y : type-Group G) →
    left-sim-congruence-Normal-Subgroup x y →
    sim-congruence-Normal-Subgroup x y
  sim-left-sim-congruence-Normal-Subgroup x y H =
    is-closed-under-eq-Normal-Subgroup G N
      ( is-normal-Normal-Subgroup' G N x
        ( inv-Group G (right-div-Group G x y))
        ( is-closed-under-inverses-Normal-Subgroup G N H))
      ( ( ap (conjugation-Group' G x) (inv-right-div-Group G x y)) ∙
        ( conjugation-right-div-Group G y x))
```

#### The standard similarity relation is a congruence relation

```agda
  refl-congruence-Normal-Subgroup :
    is-reflexive sim-congruence-Normal-Subgroup
  refl-congruence-Normal-Subgroup =
    refl-right-sim-Subgroup G (subgroup-Normal-Subgroup G N)

  symmetric-congruence-Normal-Subgroup :
    is-symmetric sim-congruence-Normal-Subgroup
  symmetric-congruence-Normal-Subgroup =
    symmetric-right-sim-Subgroup G (subgroup-Normal-Subgroup G N)

  transitive-congruence-Normal-Subgroup :
    is-transitive sim-congruence-Normal-Subgroup
  transitive-congruence-Normal-Subgroup =
    transitive-right-sim-Subgroup G (subgroup-Normal-Subgroup G N)

  equivalence-relation-congruence-Normal-Subgroup :
    equivalence-relation l2 (type-Group G)
  equivalence-relation-congruence-Normal-Subgroup =
    right-equivalence-relation-Subgroup G (subgroup-Normal-Subgroup G N)

  relate-same-elements-left-sim-congruence-Normal-Subgroup :
    relate-same-elements-equivalence-relation
      ( equivalence-relation-congruence-Normal-Subgroup)
      ( left-equivalence-relation-congruence-Normal-Subgroup)
  pr1 (relate-same-elements-left-sim-congruence-Normal-Subgroup x y) =
    left-sim-sim-congruence-Normal-Subgroup x y
  pr2 (relate-same-elements-left-sim-congruence-Normal-Subgroup x y) =
    sim-left-sim-congruence-Normal-Subgroup x y

  mul-congruence-Normal-Subgroup :
    is-congruence-Group G equivalence-relation-congruence-Normal-Subgroup
  mul-congruence-Normal-Subgroup
    {x} {x'} {y} {y'} p q =
    is-closed-under-eq-Normal-Subgroup G N
      ( closure-property-Normal-Subgroup G N p q)
      ( ( ap
          ( mul-Group' G y')
          ( ( inv
              ( associative-mul-Group G
                ( inv-Group G y)
                ( inv-Group G x)
                ( x'))) ∙
            ( ap
              ( mul-Group' G x')
              ( inv (distributive-inv-mul-Group G))))) ∙
        ( associative-mul-Group G
          ( inv-Group G (mul-Group G x y))
          ( x')
          ( y')))

  congruence-Normal-Subgroup : congruence-Group l2 G
  pr1 congruence-Normal-Subgroup =
    equivalence-relation-congruence-Normal-Subgroup
  pr2 congruence-Normal-Subgroup =
    mul-congruence-Normal-Subgroup

  inv-congruence-Normal-Subgroup :
    {x y : type-Group G} →
    sim-congruence-Normal-Subgroup x y →
    sim-congruence-Normal-Subgroup (inv-Group G x) (inv-Group G y)
  inv-congruence-Normal-Subgroup =
    inv-congruence-Group G congruence-Normal-Subgroup

  unit-congruence-Normal-Subgroup :
    {x : type-Group G} →
    sim-congruence-Normal-Subgroup x (unit-Group G) →
    is-in-Normal-Subgroup G N x
  unit-congruence-Normal-Subgroup {x} H =
    is-closed-under-inverses-Normal-Subgroup' G N x
      ( is-closed-under-eq-Normal-Subgroup G N H
        ( right-unit-law-mul-Group G (inv-Group G x)))

  unit-congruence-Normal-Subgroup' :
    {x : type-Group G} →
    is-in-Normal-Subgroup G N x →
    sim-congruence-Normal-Subgroup x (unit-Group G)
  unit-congruence-Normal-Subgroup' {x} H =
    is-closed-under-eq-Normal-Subgroup' G N
      ( is-closed-under-inverses-Normal-Subgroup G N H)
      ( right-unit-law-mul-Group G (inv-Group G x))
```

#### The normal subgroup obtained from a congruence relation

```agda
module _
  {l1 l2 : Level} (G : Group l1) (R : congruence-Group l2 G)
  where

  subset-congruence-Group : subset-Group l2 G
  subset-congruence-Group = prop-congruence-Group G R (unit-Group G)

  is-in-subset-congruence-Group : (type-Group G) → UU l2
  is-in-subset-congruence-Group = type-Prop ∘ subset-congruence-Group

  contains-unit-subset-congruence-Group :
    contains-unit-subset-Group G subset-congruence-Group
  contains-unit-subset-congruence-Group =
    refl-congruence-Group G R (unit-Group G)

  is-closed-under-multiplication-subset-congruence-Group :
    is-closed-under-multiplication-subset-Group G subset-congruence-Group
  is-closed-under-multiplication-subset-congruence-Group H K =
    concatenate-eq-sim-congruence-Group G R
      ( inv (left-unit-law-mul-Group G (unit-Group G)))
      ( mul-congruence-Group G R H K)

  is-closed-under-inverses-subset-congruence-Group :
    is-closed-under-inverses-subset-Group G subset-congruence-Group
  is-closed-under-inverses-subset-congruence-Group H =
    concatenate-eq-sim-congruence-Group G R
      ( inv (inv-unit-Group G))
      ( inv-congruence-Group G R H)

  subgroup-congruence-Group : Subgroup l2 G
  pr1 subgroup-congruence-Group = subset-congruence-Group
  pr1 (pr2 subgroup-congruence-Group) =
    contains-unit-subset-congruence-Group
  pr1 (pr2 (pr2 subgroup-congruence-Group)) =
    is-closed-under-multiplication-subset-congruence-Group
  pr2 (pr2 (pr2 subgroup-congruence-Group)) =
    is-closed-under-inverses-subset-congruence-Group

  is-normal-subgroup-congruence-Group :
    is-normal-Subgroup G subgroup-congruence-Group
  is-normal-subgroup-congruence-Group x (pair y H) =
    concatenate-eq-sim-congruence-Group G R
      ( inv (conjugation-unit-Group G x))
      ( conjugation-congruence-Group G R x H)

  normal-subgroup-congruence-Group : Normal-Subgroup l2 G
  pr1 normal-subgroup-congruence-Group = subgroup-congruence-Group
  pr2 normal-subgroup-congruence-Group =
    is-normal-subgroup-congruence-Group
```

#### The normal subgroup obtained from the congruence relation of a normal subgroup `N` is `N` itself

```agda
has-same-elements-normal-subgroup-congruence-Group :
  {l1 l2 : Level} (G : Group l1) (N : Normal-Subgroup l2 G) →
  has-same-elements-Normal-Subgroup G
    ( normal-subgroup-congruence-Group G (congruence-Normal-Subgroup G N))
    ( N)
pr1 (has-same-elements-normal-subgroup-congruence-Group G N x) H =
  is-closed-under-eq-Normal-Subgroup G N H
    ( ap (mul-Group' G x) (inv-unit-Group G) ∙ left-unit-law-mul-Group G x)
pr2 (has-same-elements-normal-subgroup-congruence-Group G N x) H =
  is-closed-under-eq-Normal-Subgroup' G N H
    ( ap (mul-Group' G x) (inv-unit-Group G) ∙ left-unit-law-mul-Group G x)

is-retraction-normal-subgroup-congruence-Group :
  {l1 l2 : Level} (G : Group l1) (N : Normal-Subgroup l2 G) →
  ( normal-subgroup-congruence-Group G
    ( congruence-Normal-Subgroup G N)) ＝
  ( N)
is-retraction-normal-subgroup-congruence-Group G N =
  eq-has-same-elements-Normal-Subgroup G
    ( normal-subgroup-congruence-Group G (congruence-Normal-Subgroup G N))
    ( N)
    ( has-same-elements-normal-subgroup-congruence-Group G N)
```

#### The congruence relation of the normal subgroup obtained from a congruence relation `R` is `R` itself

```agda
relate-same-elements-congruence-normal-subgroup-congruence-Group :
  {l1 l2 : Level} (G : Group l1) (R : congruence-Group l2 G) →
  relate-same-elements-congruence-Group G
    ( congruence-Normal-Subgroup G
      ( normal-subgroup-congruence-Group G R))
    ( R)
pr1
  ( relate-same-elements-congruence-normal-subgroup-congruence-Group
    G R x y) H =
  binary-tr
    ( sim-congruence-Group G R)
    ( right-unit-law-mul-Group G x)
    ( is-section-left-div-Group G x y)
    ( left-mul-congruence-Group G R x H)
pr2
  ( relate-same-elements-congruence-normal-subgroup-congruence-Group
    G R x y) H =
  symmetric-congruence-Group G R
    ( left-div-Group G x y)
    ( unit-Group G)
    ( map-sim-left-div-unit-congruence-Group G R H)

is-section-normal-subgroup-congruence-Group :
  {l1 l2 : Level} (G : Group l1) (R : congruence-Group l2 G) →
  ( congruence-Normal-Subgroup G
    ( normal-subgroup-congruence-Group G R)) ＝
  ( R)
is-section-normal-subgroup-congruence-Group G R =
  eq-relate-same-elements-congruence-Group G
    ( congruence-Normal-Subgroup G
      ( normal-subgroup-congruence-Group G R))
    ( R)
    ( relate-same-elements-congruence-normal-subgroup-congruence-Group G R)
```

#### The equivalence of normal subgroups and congruence relations

```agda
is-equiv-congruence-Normal-Subgroup :
  {l1 l2 : Level} (G : Group l1) →
  is-equiv (congruence-Normal-Subgroup {l1} {l2} G)
is-equiv-congruence-Normal-Subgroup G =
  is-equiv-is-invertible
    ( normal-subgroup-congruence-Group G)
    ( is-section-normal-subgroup-congruence-Group G)
    ( is-retraction-normal-subgroup-congruence-Group G)

equiv-congruence-Normal-Subgroup :
  {l1 l2 : Level} (G : Group l1) →
  Normal-Subgroup l2 G ≃ congruence-Group l2 G
pr1 (equiv-congruence-Normal-Subgroup G) =
  congruence-Normal-Subgroup G
pr2 (equiv-congruence-Normal-Subgroup G) =
  is-equiv-congruence-Normal-Subgroup G

is-equiv-normal-subgroup-congruence-Group :
  {l1 l2 : Level} (G : Group l1) →
  is-equiv (normal-subgroup-congruence-Group {l1} {l2} G)
is-equiv-normal-subgroup-congruence-Group G =
  is-equiv-is-invertible
    ( congruence-Normal-Subgroup G)
    ( is-retraction-normal-subgroup-congruence-Group G)
    ( is-section-normal-subgroup-congruence-Group G)

equiv-normal-subgroup-congruence-Group :
  {l1 l2 : Level} (G : Group l1) →
  congruence-Group l2 G ≃ Normal-Subgroup l2 G
pr1 (equiv-normal-subgroup-congruence-Group G) =
  normal-subgroup-congruence-Group G
pr2 (equiv-normal-subgroup-congruence-Group G) =
  is-equiv-normal-subgroup-congruence-Group G
```
