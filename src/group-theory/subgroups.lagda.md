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
open import foundation.disjunction
open import foundation.embeddings
open import foundation.equivalence-relations
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.large-binary-relations
open import foundation.logical-equivalences
open import foundation.powersets
open import foundation.propositional-truncations
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
open import group-theory.subsemigroups
open import group-theory.subsets-groups

open import order-theory.large-posets
open import order-theory.large-preorders
open import order-theory.order-preserving-maps-large-posets
open import order-theory.order-preserving-maps-large-preorders
open import order-theory.posets
open import order-theory.preorders
open import order-theory.similarity-of-elements-large-posets
```

</details>

## Definitions

### Subgroups

```agda
module _
  {l1 l2 : Level} (G : Group l1) (P : subset-Group l2 G)
  where

  contains-unit-prop-subset-Group : Prop l2
  contains-unit-prop-subset-Group = P (unit-Group G)

  contains-unit-subset-Group : UU l2
  contains-unit-subset-Group =
    type-Prop contains-unit-prop-subset-Group

  is-prop-contains-unit-subset-Group :
    is-prop contains-unit-subset-Group
  is-prop-contains-unit-subset-Group =
    is-prop-type-Prop contains-unit-prop-subset-Group

  is-closed-under-multiplication-prop-subset-Group : Prop (l1 ⊔ l2)
  is-closed-under-multiplication-prop-subset-Group =
    is-closed-under-multiplication-prop-subset-Semigroup
      ( semigroup-Group G)
      ( P)

  is-closed-under-multiplication-subset-Group : UU (l1 ⊔ l2)
  is-closed-under-multiplication-subset-Group =
    type-Prop is-closed-under-multiplication-prop-subset-Group

  is-prop-is-closed-under-multiplication-subset-Group :
    is-prop is-closed-under-multiplication-subset-Group
  is-prop-is-closed-under-multiplication-subset-Group =
    is-prop-type-Prop is-closed-under-multiplication-prop-subset-Group

  is-closed-under-inverses-prop-subset-Group : Prop (l1 ⊔ l2)
  is-closed-under-inverses-prop-subset-Group =
    implicit-Π-Prop
      ( type-Group G)
      ( λ x → hom-Prop (P x) (P (inv-Group G x)))

  is-closed-under-inverses-subset-Group : UU (l1 ⊔ l2)
  is-closed-under-inverses-subset-Group =
    type-Prop is-closed-under-inverses-prop-subset-Group

  is-prop-is-closed-under-inverses-subset-Group :
    is-prop is-closed-under-inverses-subset-Group
  is-prop-is-closed-under-inverses-subset-Group =
    is-prop-type-Prop is-closed-under-inverses-prop-subset-Group

  is-subgroup-prop-subset-Group : Prop (l1 ⊔ l2)
  is-subgroup-prop-subset-Group =
    product-Prop
      ( contains-unit-prop-subset-Group)
      ( product-Prop
        ( is-closed-under-multiplication-prop-subset-Group)
        ( is-closed-under-inverses-prop-subset-Group))

  is-subgroup-subset-Group : UU (l1 ⊔ l2)
  is-subgroup-subset-Group = type-Prop is-subgroup-prop-subset-Group

  is-prop-is-subgroup-subset-Group : is-prop is-subgroup-subset-Group
  is-prop-is-subgroup-subset-Group =
    is-prop-type-Prop is-subgroup-prop-subset-Group
```

### The type of all subgroups of a group

```agda
Subgroup : (l : Level) {l1 : Level} (G : Group l1) → UU (lsuc l ⊔ l1)
Subgroup l G = type-subtype (is-subgroup-prop-subset-Group {l2 = l} G)

module _
  {l1 l2 : Level} (G : Group l1) (H : Subgroup l2 G)
  where

  subset-Subgroup : subset-Group l2 G
  subset-Subgroup =
    inclusion-subtype (is-subgroup-prop-subset-Group G) H

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

  is-closed-under-inverses-Subgroup :
    is-closed-under-inverses-subset-Group G subset-Subgroup
  is-closed-under-inverses-Subgroup = pr2 (pr2 is-subgroup-Subgroup)

  is-closed-under-inverses-Subgroup' :
    (x : type-Group G) →
    is-in-Subgroup (inv-Group G x) → is-in-Subgroup x
  is-closed-under-inverses-Subgroup' x p =
    is-closed-under-eq-Subgroup
      ( is-closed-under-inverses-Subgroup p)
      ( inv-inv-Group G x)

  is-in-subgroup-left-factor-Subgroup :
    (x y : type-Group G) →
    is-in-Subgroup (mul-Group G x y) → is-in-Subgroup y →
    is-in-Subgroup x
  is-in-subgroup-left-factor-Subgroup x y p q =
    is-closed-under-eq-Subgroup
      ( is-closed-under-multiplication-Subgroup
        ( p)
        ( is-closed-under-inverses-Subgroup q))
      ( is-retraction-right-div-Group G y x)

  is-in-subgroup-right-factor-Subgroup :
    (x y : type-Group G) →
    is-in-Subgroup (mul-Group G x y) → is-in-Subgroup x →
    is-in-Subgroup y
  is-in-subgroup-right-factor-Subgroup x y p q =
    is-closed-under-eq-Subgroup
      ( is-closed-under-multiplication-Subgroup
        ( is-closed-under-inverses-Subgroup q)
        ( p))
      ( is-retraction-left-div-Group G x y)

  is-closed-under-powers-int-Subgroup :
    (k : ℤ) (x : type-Group G) →
    is-in-Subgroup x → is-in-Subgroup (integer-power-Group G k x)
  is-closed-under-powers-int-Subgroup (inl zero-ℕ) x H =
    is-closed-under-eq-Subgroup'
      ( is-closed-under-inverses-Subgroup H)
      ( right-unit-law-mul-Group G (inv-Group G x))
  is-closed-under-powers-int-Subgroup (inl (succ-ℕ k)) x H =
    is-closed-under-multiplication-Subgroup
      ( is-closed-under-inverses-Subgroup H)
      ( is-closed-under-powers-int-Subgroup (inl k) x H)
  is-closed-under-powers-int-Subgroup (inr (inl _)) x H =
    contains-unit-Subgroup
  is-closed-under-powers-int-Subgroup (inr (inr zero-ℕ)) x H =
    is-closed-under-eq-Subgroup' H (right-unit-law-mul-Group G x)
  is-closed-under-powers-int-Subgroup (inr (inr (succ-ℕ k))) x H =
    is-closed-under-multiplication-Subgroup
      ( H)
      ( is-closed-under-powers-int-Subgroup (inr (inr k)) x H)

  subsemigroup-Subgroup : Subsemigroup l2 (semigroup-Group G)
  pr1 subsemigroup-Subgroup = subset-Subgroup
  pr2 subsemigroup-Subgroup = is-closed-under-multiplication-Subgroup

is-emb-subset-Subgroup :
  {l1 l2 : Level} (G : Group l1) →
  is-emb (subset-Subgroup {l2 = l2} G)
is-emb-subset-Subgroup G =
  is-emb-inclusion-subtype (is-subgroup-prop-subset-Group G)
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
    is-closed-under-multiplication-Subgroup G H (pr2 x) (pr2 y)

  associative-mul-Subgroup :
    (x y z : type-group-Subgroup) →
    mul-Subgroup (mul-Subgroup x y) z ＝
    mul-Subgroup x (mul-Subgroup y z)
  associative-mul-Subgroup x y z =
    eq-subgroup-eq-group
      ( associative-mul-Group G (pr1 x) (pr1 y) (pr1 z))

  unit-Subgroup : type-group-Subgroup
  pr1 unit-Subgroup = unit-Group G
  pr2 unit-Subgroup = contains-unit-Subgroup G H

  left-unit-law-mul-Subgroup :
    (x : type-group-Subgroup) → mul-Subgroup unit-Subgroup x ＝ x
  left-unit-law-mul-Subgroup x =
    eq-subgroup-eq-group (left-unit-law-mul-Group G (pr1 x))

  right-unit-law-mul-Subgroup :
    (x : type-group-Subgroup) → mul-Subgroup x unit-Subgroup ＝ x
  right-unit-law-mul-Subgroup x =
    eq-subgroup-eq-group (right-unit-law-mul-Group G (pr1 x))

  inv-Subgroup : type-group-Subgroup → type-group-Subgroup
  pr1 (inv-Subgroup x) = inv-Group G (pr1 x)
  pr2 (inv-Subgroup x) =
    is-closed-under-inverses-Subgroup G H (pr2 x)

  left-inverse-law-mul-Subgroup :
    ( x : type-group-Subgroup) →
    mul-Subgroup (inv-Subgroup x) x ＝ unit-Subgroup
  left-inverse-law-mul-Subgroup x =
    eq-subgroup-eq-group (left-inverse-law-mul-Group G (pr1 x))

  right-inverse-law-mul-Subgroup :
    (x : type-group-Subgroup) →
    mul-Subgroup x (inv-Subgroup x) ＝ unit-Subgroup
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
  preserves-mul-inclusion-Subgroup = refl

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
  preserves-inverses-inclusion-Subgroup = refl

  hom-inclusion-Subgroup :
    hom-Group (group-Subgroup G H) G
  pr1 hom-inclusion-Subgroup = inclusion-Subgroup G H
  pr2 hom-inclusion-Subgroup {x} {y} = preserves-mul-inclusion-Subgroup {x} {y}
```

## Properties

### Extensionality of the type of all subgroups

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Subgroup l2 G)
  where

  has-same-elements-prop-Subgroup :
    {l3 : Level} → Subgroup l3 G → Prop (l1 ⊔ l2 ⊔ l3)
  has-same-elements-prop-Subgroup K =
    has-same-elements-subtype-Prop
      ( subset-Subgroup G H)
      ( subset-Subgroup G K)

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
      ( is-subgroup-prop-subset-Group G)
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
leq-prop-Subgroup :
  {l1 l2 l3 : Level} (G : Group l1) →
  Subgroup l2 G → Subgroup l3 G → Prop (l1 ⊔ l2 ⊔ l3)
leq-prop-Subgroup G H K =
  leq-prop-subtype
    ( subset-Subgroup G H)
    ( subset-Subgroup G K)

leq-Subgroup :
  {l1 l2 l3 : Level} (G : Group l1) →
  Subgroup l2 G → Subgroup l3 G → UU (l1 ⊔ l2 ⊔ l3)
leq-Subgroup G H K = subset-Subgroup G H ⊆ subset-Subgroup G K

is-prop-leq-Subgroup :
  {l1 l2 l3 : Level} (G : Group l1) →
  (H : Subgroup l2 G) (K : Subgroup l3 G) →
  is-prop (leq-Subgroup G H K)
is-prop-leq-Subgroup G H K =
  is-prop-leq-subtype (subset-Subgroup G H) (subset-Subgroup G K)

refl-leq-Subgroup :
  {l1 : Level} (G : Group l1) →
  is-reflexive-Large-Relation (λ l → Subgroup l G) (leq-Subgroup G)
refl-leq-Subgroup G H = refl-leq-subtype (subset-Subgroup G H)

transitive-leq-Subgroup :
  {l1 : Level} (G : Group l1) →
  is-transitive-Large-Relation (λ l → Subgroup l G) (leq-Subgroup G)
transitive-leq-Subgroup G H K L =
  transitive-leq-subtype
    ( subset-Subgroup G H)
    ( subset-Subgroup G K)
    ( subset-Subgroup G L)

antisymmetric-leq-Subgroup :
  {l1 : Level} (G : Group l1) →
  is-antisymmetric-Large-Relation (λ l → Subgroup l G) (leq-Subgroup G)
antisymmetric-leq-Subgroup G H K α β =
  eq-has-same-elements-Subgroup G H K (λ x → (α x , β x))

Subgroup-Large-Preorder :
  {l1 : Level} (G : Group l1) →
  Large-Preorder (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
type-Large-Preorder (Subgroup-Large-Preorder G) l2 = Subgroup l2 G
leq-prop-Large-Preorder (Subgroup-Large-Preorder G) H K =
  leq-prop-Subgroup G H K
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
    ( λ l → l)
    ( Subgroup-Large-Poset G)
    ( powerset-Large-Poset (type-Group G))
map-hom-Large-Preorder
  ( subset-subgroup-hom-large-poset-Group G) =
  subset-Subgroup G
preserves-order-hom-Large-Preorder
  ( subset-subgroup-hom-large-poset-Group G) =
  preserves-order-subset-Subgroup G
```

### The type of subgroups of a group is a set

```agda
module _
  {l1 : Level} (G : Group l1)
  where

  is-set-Subgroup : {l2 : Level} → is-set (Subgroup l2 G)
  is-set-Subgroup = is-set-type-Poset (Subgroup-Poset _ G)
```

### Subgroups have the same elements if and only if they are similar in the poset of subgroups

**Note:** We don't abbreviate the word `similar` in the name of the similarity
relation on subgroups, because below we will define for each subgroup `H` of `G`
two equivalence relations on `G`, which we will call `right-sim-Subgroup` and
`left-sim-Subgroup`.

```agda
module _
  {l1 l2 l3 : Level} (G : Group l1) (H : Subgroup l2 G) (K : Subgroup l3 G)
  where

  similar-Subgroup : UU (l1 ⊔ l2 ⊔ l3)
  similar-Subgroup = sim-Large-Poset (Subgroup-Large-Poset G) H K

  has-same-elements-similar-Subgroup :
    similar-Subgroup → has-same-elements-Subgroup G H K
  pr1 (has-same-elements-similar-Subgroup (s , t) x) = s x
  pr2 (has-same-elements-similar-Subgroup (s , t) x) = t x

  leq-has-same-elements-Subgroup :
    has-same-elements-Subgroup G H K → leq-Subgroup G H K
  leq-has-same-elements-Subgroup s x = forward-implication (s x)

  leq-has-same-elements-Subgroup' :
    has-same-elements-Subgroup G H K → leq-Subgroup G K H
  leq-has-same-elements-Subgroup' s x = backward-implication (s x)

  similar-has-same-elements-Subgroup :
    has-same-elements-Subgroup G H K → similar-Subgroup
  pr1 (similar-has-same-elements-Subgroup s) = leq-has-same-elements-Subgroup s
  pr2 (similar-has-same-elements-Subgroup s) = leq-has-same-elements-Subgroup' s
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

  prop-right-equivalence-relation-Subgroup : (x y : type-Group G) → Prop l2
  pr1 (prop-right-equivalence-relation-Subgroup x y) = right-sim-Subgroup x y
  pr2 (prop-right-equivalence-relation-Subgroup x y) =
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
      ( is-closed-under-inverses-Subgroup G H p)

  transitive-right-sim-Subgroup : is-transitive right-sim-Subgroup
  transitive-right-sim-Subgroup x y z p q =
    tr
      ( is-in-Subgroup G H)
      ( mul-left-div-Group G x y z)
      ( is-closed-under-multiplication-Subgroup G H
        ( q)
        ( p))

  right-equivalence-relation-Subgroup : equivalence-relation l2 (type-Group G)
  pr1 right-equivalence-relation-Subgroup =
    prop-right-equivalence-relation-Subgroup
  pr1 (pr2 right-equivalence-relation-Subgroup) = refl-right-sim-Subgroup
  pr1 (pr2 (pr2 right-equivalence-relation-Subgroup)) =
    symmetric-right-sim-Subgroup
  pr2 (pr2 (pr2 right-equivalence-relation-Subgroup)) =
    transitive-right-sim-Subgroup
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

  prop-left-equivalence-relation-Subgroup : (x y : type-Group G) → Prop l2
  pr1 (prop-left-equivalence-relation-Subgroup x y) = left-sim-Subgroup x y
  pr2 (prop-left-equivalence-relation-Subgroup x y) =
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
      ( is-closed-under-inverses-Subgroup G H p)

  transitive-left-sim-Subgroup : is-transitive left-sim-Subgroup
  transitive-left-sim-Subgroup x y z p q =
    tr
      ( is-in-Subgroup G H)
      ( mul-right-div-Group G x y z)
      ( is-closed-under-multiplication-Subgroup G H q p)

  left-equivalence-relation-Subgroup : equivalence-relation l2 (type-Group G)
  pr1 left-equivalence-relation-Subgroup =
    prop-left-equivalence-relation-Subgroup
  pr1 (pr2 left-equivalence-relation-Subgroup) = refl-left-sim-Subgroup
  pr1 (pr2 (pr2 left-equivalence-relation-Subgroup)) =
    symmetric-left-sim-Subgroup
  pr2 (pr2 (pr2 left-equivalence-relation-Subgroup)) =
    transitive-left-sim-Subgroup
```

### Any proposition `P` induces a subgroup of any group `G`

The subset consisting of elements `x : G` such that `(1 ＝ x) ∨ P` holds is
always a subgroup of `G`. This subgroup consists only of the unit element if `P`
is false, and it is the [full subgroup](group-theory.full-subgroups.md) if `P`
is true.

```agda
module _
  {l1 l2 : Level} (G : Group l1) (P : Prop l2)
  where

  subset-subgroup-Prop : subset-Group (l1 ⊔ l2) G
  subset-subgroup-Prop x =
    disjunction-Prop (Id-Prop (set-Group G) (unit-Group G) x) P

  contains-unit-subgroup-Prop :
    contains-unit-subset-Group G subset-subgroup-Prop
  contains-unit-subgroup-Prop = inl-disjunction refl

  is-closed-under-multiplication-subgroup-Prop' :
    (x y : type-Group G) →
    ((unit-Group G ＝ x) + type-Prop P) →
    ((unit-Group G ＝ y) + type-Prop P) →
    ((unit-Group G ＝ mul-Group G x y) + type-Prop P)
  is-closed-under-multiplication-subgroup-Prop' ._ ._ (inl refl) (inl refl) =
    inl (inv (left-unit-law-mul-Group G _))
  is-closed-under-multiplication-subgroup-Prop' ._ y (inl refl) (inr q) =
    inr q
  is-closed-under-multiplication-subgroup-Prop' x y (inr p) (inl β) =
    inr p
  is-closed-under-multiplication-subgroup-Prop' x y (inr p) (inr q) =
    inr p

  is-closed-under-multiplication-subgroup-Prop :
    is-closed-under-multiplication-subset-Group G subset-subgroup-Prop
  is-closed-under-multiplication-subgroup-Prop H K =
    apply-twice-universal-property-trunc-Prop H K
      ( disjunction-Prop (Id-Prop (set-Group G) _ _) P)
      ( λ H' K' →
        unit-trunc-Prop
          ( is-closed-under-multiplication-subgroup-Prop' _ _ H' K'))

  is-closed-under-inverses-subgroup-Prop' :
    {x : type-Group G} → ((unit-Group G ＝ x) + type-Prop P) →
    ((unit-Group G ＝ inv-Group G x) + type-Prop P)
  is-closed-under-inverses-subgroup-Prop' (inl refl) =
    inl (inv (inv-unit-Group G))
  is-closed-under-inverses-subgroup-Prop' (inr p) =
    inr p

  is-closed-under-inverses-subgroup-Prop :
    is-closed-under-inverses-subset-Group G subset-subgroup-Prop
  is-closed-under-inverses-subgroup-Prop {x} H =
    apply-universal-property-trunc-Prop H
      ( disjunction-Prop (Id-Prop (set-Group G) _ _) P)
      ( unit-trunc-Prop ∘ is-closed-under-inverses-subgroup-Prop')

  subgroup-Prop : Subgroup (l1 ⊔ l2) G
  pr1 subgroup-Prop = subset-subgroup-Prop
  pr1 (pr2 subgroup-Prop) = contains-unit-subgroup-Prop
  pr1 (pr2 (pr2 subgroup-Prop)) = is-closed-under-multiplication-subgroup-Prop
  pr2 (pr2 (pr2 subgroup-Prop)) = is-closed-under-inverses-subgroup-Prop

  group-subgroup-Prop : Group (l1 ⊔ l2)
  group-subgroup-Prop = group-Subgroup G subgroup-Prop
```

## See also

- [Monomorphisms in the category of groups](group-theory.monomorphisms-groups.md)
- [Normal subgroups](group-theory.normal-subgroups.md)
- [Submonoids](group-theory.submonoids.md)

## External links

- [Subgroups](https://1lab.dev/Algebra.Group.Subgroup.html) at 1lab
- [subgroup](https://ncatlab.org/nlab/show/subgroup) at $n$Lab
- [Subgroup](https://en.wikipedia.org/wiki/Subgroup) at Wikipedia
- [Subgroup](https://mathworld.wolfram.com/Subgroup.html) at Wolfram MathWorld
- [subgroup](https://www.wikidata.org/wiki/Q466109) at Wikidata
