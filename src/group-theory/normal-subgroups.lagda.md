# Normal subgroups

```agda
module group-theory.normal-subgroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equational-reasoning
open import foundation.equivalence-relations
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.functions
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositional-maps
open import foundation.propositions
open import foundation.subtype-identity-principle
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.congruence-relations-groups
open import group-theory.conjugation
open import group-theory.groups
open import group-theory.subgroups

open import order-theory.large-posets
open import order-theory.large-preorders
open import order-theory.posets
open import order-theory.preorders
```

</details>

## Idea

A normal subgroup of `G` is a subgroup `H` of `G` which is closed under conjugation.

## Definition

```agda
is-normal-subgroup-Prop :
  {l1 l2 : Level} (G : Group l1) (H : Subgroup l2 G) → Prop (l1 ⊔ l2)
is-normal-subgroup-Prop G H =
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
is-normal-Subgroup G H = type-Prop (is-normal-subgroup-Prop G H)

is-prop-is-normal-Subgroup :
  {l1 l2 : Level} (G : Group l1) (H : Subgroup l2 G) →
  is-prop (is-normal-Subgroup G H)
is-prop-is-normal-Subgroup G H =
  is-prop-type-Prop (is-normal-subgroup-Prop G H)

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
is-normal-is-normal-Subgroup' G H  K x y =
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

  is-closed-under-mul-Normal-Subgroup :
    is-closed-under-mul-subset-Group G subset-Normal-Subgroup
  is-closed-under-mul-Normal-Subgroup =
    is-closed-under-mul-Subgroup G subgroup-Normal-Subgroup

  mul-Normal-Subgroup :
    type-Normal-Subgroup → type-Normal-Subgroup → type-Normal-Subgroup
  mul-Normal-Subgroup = mul-Subgroup G subgroup-Normal-Subgroup

  is-closed-under-inv-Normal-Subgroup :
    is-closed-under-inv-subset-Group G subset-Normal-Subgroup
  is-closed-under-inv-Normal-Subgroup =
    is-closed-under-inv-Subgroup G subgroup-Normal-Subgroup

  inv-Normal-Subgroup : type-Normal-Subgroup → type-Normal-Subgroup
  inv-Normal-Subgroup = inv-Subgroup G subgroup-Normal-Subgroup

  is-closed-under-inv-Normal-Subgroup' :
    (x : type-Group G) →
    is-in-Normal-Subgroup (inv-Group G x) → is-in-Normal-Subgroup x
  is-closed-under-inv-Normal-Subgroup' =
    is-closed-under-inv-Subgroup' G subgroup-Normal-Subgroup

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

  is-normal-subgroup-Normal-Subgroup :
    (x y : type-Group G) → is-in-Normal-Subgroup y →
    is-in-Normal-Subgroup (conjugation-Group G x y)
  is-normal-subgroup-Normal-Subgroup x y p = pr2 N x (y , p)

  is-normal-subgroup-Normal-Subgroup' :
    (x y : type-Group G) → is-in-Normal-Subgroup y →
    is-in-Normal-Subgroup (conjugation-Group' G x y)
  is-normal-subgroup-Normal-Subgroup' x y p =
    is-normal-is-normal-Subgroup G
      ( subgroup-Normal-Subgroup)
      ( λ x y → is-normal-subgroup-Normal-Subgroup x (pr1 y) (pr2 y))
      ( x)
      ( pair y p)

  closure-property-Normal-Subgroup :
    {x y z : type-Group G} →
    is-in-Normal-Subgroup y →
    is-in-Normal-Subgroup (mul-Group G x z) →
    is-in-Normal-Subgroup (mul-Group G (mul-Group G x y) z)
  closure-property-Normal-Subgroup {x} {y} {z} p q =
    is-closed-under-eq-Normal-Subgroup
      ( is-closed-under-mul-Normal-Subgroup
        ( conjugation-Group G x y)
        ( mul-Group G x z)
        ( is-normal-subgroup-Normal-Subgroup x y p)
        ( q))
      ( ( associative-mul-Group G
          ( mul-Group G x y)
          ( inv-Group G x)
          ( mul-Group G x z)) ∙
        ( ap
          ( mul-Group G (mul-Group G x y))
          ( isretr-mul-inv-Group G x z)))

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
    is-normal-subgroup-Normal-Subgroup y (pr1 u) (pr2 u)

  conjugation-Normal-Subgroup' :
    type-Group G → type-Normal-Subgroup → type-Normal-Subgroup
  pr1 (conjugation-Normal-Subgroup' y u) =
    conjugation-Group' G y (inclusion-Normal-Subgroup u)
  pr2 (conjugation-Normal-Subgroup' y u) =
    is-normal-subgroup-Normal-Subgroup' y (pr1 u) (pr2 u)
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
      ( is-normal-subgroup-Prop G)
      ( λ x y →
        is-normal-subgroup-Normal-Subgroup G N x (pr1 y) (pr2 y))
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
contains-Normal-Subgroup-Prop :
  {l1 l2 l3 : Level} (G : Group l1) →
  Normal-Subgroup l2 G → Normal-Subgroup l3 G → Prop (l1 ⊔ l2 ⊔ l3)
contains-Normal-Subgroup-Prop G H K =
  contains-Subgroup-Prop G
    ( subgroup-Normal-Subgroup G H)
    ( subgroup-Normal-Subgroup G K)

contains-Normal-Subgroup :
  {l1 l2 l3 : Level} (G : Group l1) →
  Normal-Subgroup l2 G → Normal-Subgroup l3 G → UU (l1 ⊔ l2 ⊔ l3)
contains-Normal-Subgroup G H K =
  contains-Subgroup G
    ( subgroup-Normal-Subgroup G H)
    ( subgroup-Normal-Subgroup G K)

refl-contains-Normal-Subgroup :
  {l1 l2 : Level} (G : Group l1) (H : Normal-Subgroup l2 G) →
  contains-Normal-Subgroup G H H
refl-contains-Normal-Subgroup G H =
  refl-contains-Subgroup G (subgroup-Normal-Subgroup G H)

transitive-contains-Normal-Subgroup :
  {l1 l2 l3 l4 : Level} (G : Group l1) (H : Normal-Subgroup l2 G)
  (K : Normal-Subgroup l3 G) (L : Normal-Subgroup l4 G) →
  contains-Normal-Subgroup G K L → contains-Normal-Subgroup G H K →
  contains-Normal-Subgroup G H L
transitive-contains-Normal-Subgroup G H K L =
  transitive-contains-Subgroup G
    ( subgroup-Normal-Subgroup G H)
    ( subgroup-Normal-Subgroup G K)
    ( subgroup-Normal-Subgroup G L)

antisymmetric-contains-Normal-Subgroup :
  {l1 l2 : Level} (G : Group l1) (H K : Normal-Subgroup l2 G) →
  contains-Normal-Subgroup G H K →
  contains-Normal-Subgroup G K H → H ＝ K
antisymmetric-contains-Normal-Subgroup G H K α β =
  eq-has-same-elements-Normal-Subgroup G H K (λ x → (α x , β x))

Normal-Subgroup-Large-Preorder :
  {l1 : Level} (G : Group l1) →
  Large-Preorder (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
type-Large-Preorder (Normal-Subgroup-Large-Preorder G) l2 =
  Normal-Subgroup l2 G
leq-large-preorder-Prop (Normal-Subgroup-Large-Preorder G) H K =
  contains-Normal-Subgroup-Prop G H K
refl-leq-Large-Preorder (Normal-Subgroup-Large-Preorder G) =
  refl-contains-Normal-Subgroup G
trans-leq-Large-Preorder (Normal-Subgroup-Large-Preorder G) =
  transitive-contains-Normal-Subgroup G

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
  antisymmetric-contains-Normal-Subgroup G

Normal-Subgroup-Poset :
  {l1 : Level} (l2 : Level) (G : Group l1) →
  Poset (l1 ⊔ lsuc l2) (l1 ⊔ l2)
Normal-Subgroup-Poset l2 G =
  poset-Large-Poset (Normal-Subgroup-Large-Poset G) l2
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
    prop-right-eq-rel-Subgroup G (subgroup-Normal-Subgroup G N)
```

#### The left equivalence relation obtained from a normal subgroup

```agda
  left-eq-rel-congruence-Normal-Subgroup :
    Eq-Rel l2 (type-Group G)
  left-eq-rel-congruence-Normal-Subgroup =
    left-eq-rel-Subgroup G (subgroup-Normal-Subgroup G N)

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
      ( is-normal-subgroup-Normal-Subgroup G N y
        ( inv-Group G (left-div-Group G x y))
        ( is-closed-under-inv-Normal-Subgroup G N
          ( left-div-Group G x y)
          ( H)))
      ( ( ap (conjugation-Group G y) (inv-left-div-Group G x y) ∙
        ( conjugation-left-div-Group G y x)))

  sim-left-sim-congruence-Normal-Subgroup :
    (x y : type-Group G) →
    left-sim-congruence-Normal-Subgroup x y →
    sim-congruence-Normal-Subgroup x y
  sim-left-sim-congruence-Normal-Subgroup x y H =
    is-closed-under-eq-Normal-Subgroup G N
      ( is-normal-subgroup-Normal-Subgroup' G N x
        ( inv-Group G (right-div-Group G x y))
        ( is-closed-under-inv-Normal-Subgroup G N
          ( right-div-Group G x y)
          ( H)))
      ( ( ap (conjugation-Group' G x) (inv-right-div-Group G x y)) ∙
        ( conjugation-right-div-Group G y x))
```

#### The standard similarity relation is a congruence relation

```agda
  refl-congruence-Normal-Subgroup :
    is-reflexive-Rel-Prop prop-congruence-Normal-Subgroup
  refl-congruence-Normal-Subgroup =
    refl-right-sim-Subgroup G (subgroup-Normal-Subgroup G N)

  symm-congruence-Normal-Subgroup :
    is-symmetric-Rel-Prop prop-congruence-Normal-Subgroup
  symm-congruence-Normal-Subgroup =
    symmetric-right-sim-Subgroup G (subgroup-Normal-Subgroup G N)

  trans-congruence-Normal-Subgroup :
    is-transitive-Rel-Prop prop-congruence-Normal-Subgroup
  trans-congruence-Normal-Subgroup =
    transitive-right-sim-Subgroup G (subgroup-Normal-Subgroup G N)

  eq-rel-congruence-Normal-Subgroup : Eq-Rel l2 (type-Group G)
  eq-rel-congruence-Normal-Subgroup =
    right-eq-rel-Subgroup G (subgroup-Normal-Subgroup G N)

  relate-same-elements-left-sim-congruence-Normal-Subgroup :
    relate-same-elements-Eq-Rel
      ( eq-rel-congruence-Normal-Subgroup)
      ( left-eq-rel-congruence-Normal-Subgroup)
  pr1 (relate-same-elements-left-sim-congruence-Normal-Subgroup x y) =
    left-sim-sim-congruence-Normal-Subgroup x y
  pr2 (relate-same-elements-left-sim-congruence-Normal-Subgroup x y) =
    sim-left-sim-congruence-Normal-Subgroup x y

  mul-congruence-Normal-Subgroup :
    is-congruence-Group G eq-rel-congruence-Normal-Subgroup
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
              ( inv (distributive-inv-mul-Group G x y))))) ∙
        ( associative-mul-Group G
          ( inv-Group G (mul-Group G x y))
          ( x')
          ( y')))

  congruence-Normal-Subgroup : congruence-Group l2 G
  pr1 congruence-Normal-Subgroup = eq-rel-congruence-Normal-Subgroup
  pr2 congruence-Normal-Subgroup =
    mul-congruence-Normal-Subgroup

  inv-congruence-Normal-Subgroup :
    {x y : type-Group G} →
    sim-congruence-Normal-Subgroup x y →
    sim-congruence-Normal-Subgroup (inv-Group G x) (inv-Group G y)
  inv-congruence-Normal-Subgroup =
    inv-congruence-Group G congruence-Normal-Subgroup
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
  contains-unit-subset-congruence-Group = refl-congruence-Group G R

  is-closed-under-mul-subset-congruence-Group :
    is-closed-under-mul-subset-Group G subset-congruence-Group
  is-closed-under-mul-subset-congruence-Group x y H K =
    concatenate-eq-sim-congruence-Group G R
      ( inv (left-unit-law-mul-Group G (unit-Group G)))
      ( mul-congruence-Group G R H K)

  is-closed-under-inv-subset-congruence-Group :
    is-closed-under-inv-subset-Group G subset-congruence-Group
  is-closed-under-inv-subset-congruence-Group x H =
    concatenate-eq-sim-congruence-Group G R
      ( inv (inv-unit-Group G))
      ( inv-congruence-Group G R H)

  subgroup-congruence-Group : Subgroup l2 G
  pr1 subgroup-congruence-Group = subset-congruence-Group
  pr1 (pr2 subgroup-congruence-Group) =
    contains-unit-subset-congruence-Group
  pr1 (pr2 (pr2 subgroup-congruence-Group)) =
    is-closed-under-mul-subset-congruence-Group
  pr2 (pr2 (pr2 subgroup-congruence-Group)) =
    is-closed-under-inv-subset-congruence-Group

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
    ( normal-subgroup-congruence-Group G
      ( congruence-Normal-Subgroup G N))
    ( N)
pr1 (has-same-elements-normal-subgroup-congruence-Group G N x) H =
  is-closed-under-eq-Normal-Subgroup G N H
    ( ( ap (mul-Group' G x) (inv-unit-Group G)) ∙
      ( left-unit-law-mul-Group G x))
pr2 (has-same-elements-normal-subgroup-congruence-Group G N x) H =
  is-closed-under-eq-Normal-Subgroup' G N H
    ( ( ap (mul-Group' G x) (inv-unit-Group G)) ∙
      ( left-unit-law-mul-Group G x))

isretr-normal-subgroup-congruence-Group :
  {l1 l2 : Level} (G : Group l1) (N : Normal-Subgroup l2 G) →
  ( normal-subgroup-congruence-Group G
    ( congruence-Normal-Subgroup G N)) ＝
  ( N)
isretr-normal-subgroup-congruence-Group G N =
  eq-has-same-elements-Normal-Subgroup G
    ( normal-subgroup-congruence-Group G
      ( congruence-Normal-Subgroup G N))
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
    ( issec-mul-inv-Group G x y)
    ( left-mul-congruence-Group G R x H)
pr2
  ( relate-same-elements-congruence-normal-subgroup-congruence-Group
    G R x y) H =
  symm-congruence-Group G R
    ( map-sim-left-div-unit-congruence-Group G R H)

issec-normal-subgroup-congruence-Group :
  {l1 l2 : Level} (G : Group l1) (R : congruence-Group l2 G) →
  ( congruence-Normal-Subgroup G
    ( normal-subgroup-congruence-Group G R)) ＝
  ( R)
issec-normal-subgroup-congruence-Group G R =
  eq-relate-same-elements-congruence-Group G
    ( congruence-Normal-Subgroup G
      ( normal-subgroup-congruence-Group G R))
    ( R)
    ( relate-same-elements-congruence-normal-subgroup-congruence-Group
      G R)
```

#### The equivalence of normal subgroups and congruence relations

```agda
is-equiv-congruence-Normal-Subgroup :
  {l1 l2 : Level} (G : Group l1) →
  is-equiv (congruence-Normal-Subgroup {l1} {l2} G)
is-equiv-congruence-Normal-Subgroup G =
  is-equiv-has-inverse
    ( normal-subgroup-congruence-Group G)
    ( issec-normal-subgroup-congruence-Group G)
    ( isretr-normal-subgroup-congruence-Group G)

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
  is-equiv-has-inverse
    ( congruence-Normal-Subgroup G)
    ( isretr-normal-subgroup-congruence-Group G)
    ( issec-normal-subgroup-congruence-Group G)

equiv-normal-subgroup-congruence-Group :
  {l1 l2 : Level} (G : Group l1) →
  congruence-Group l2 G ≃ Normal-Subgroup l2 G
pr1 (equiv-normal-subgroup-congruence-Group G) =
  normal-subgroup-congruence-Group G
pr2 (equiv-normal-subgroup-congruence-Group G) =
  is-equiv-normal-subgroup-congruence-Group G
```
