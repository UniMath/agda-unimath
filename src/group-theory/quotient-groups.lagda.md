# Quotient groups

```agda
module group-theory.quotient-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.binary-functoriality-set-quotients
open import foundation.commuting-triangles-of-maps
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.effective-maps-equivalence-relations
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-set-quotients
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.reflecting-maps-equivalence-relations
open import foundation.set-quotients
open import foundation.sets
open import foundation.subtypes
open import foundation.surjective-maps
open import foundation.universal-property-set-quotients
open import foundation.universe-levels

open import group-theory.groups
open import group-theory.homomorphisms-groups
open import group-theory.kernels-homomorphisms-groups
open import group-theory.normal-subgroups
open import group-theory.nullifying-group-homomorphisms
open import group-theory.semigroups
```

</details>

## Idea

Given a [normal subgroup](group-theory.normal-subgroups.md) `N` of `G`, the
{{#concept "quotient group" Agda=quotient-Group}} `G/N` is a
[group](group-theory.groups.md) equipped with a
[group homomorphism](group-theory.homomorphisms-groups.md) `q : G → G/N` such
that `N ⊆ ker q`, and such that `q` satisfies the
{{#concept "universal property of the
quotient group"}}, which asserts that any group homomorphism `f : G → H` such that
`N ⊆ ker f` extends uniquely along `q` to a group homomorphism `G/N → H`. In other
words, the universal property of the quotient group `G/N` asserts that the map

```text
  hom-Group G/N H → nullifying-hom-Group G H N
```

from group homomorphisms `G/N → H` to
[`N`-nullifying group homomorphism](group-theory.nullifying-group-homomorphisms.md)
`G → H` is an [equivalence](foundation-core.equivalences.md). Recall that a
group homomorphism is said to be `N`-nullifying if `N` is contained in the
[kernel](group-theory.kernels-homomorphisms-groups.md) of `f`.

That the quotient group satisfies its universal property is also referred to as
the
{{#concept "fundamental theorem on homomorphisms" Disambiguation="of groups" WD="fundamental theorem on homomorphisms" WDID=Q1187646 Agda=is-quotient-group-quotient-Group}},
or **first isomorphism theorem**.

## Definitions

### The universal property of quotient groups

```agda
precomp-nullifying-hom-Group :
  {l1 l2 l3 l4 : Level} (G : Group l1) (N : Normal-Subgroup l2 G)
  (H : Group l3) (f : nullifying-hom-Group G H N)
  (K : Group l4) → hom-Group H K → nullifying-hom-Group G K N
pr1 (precomp-nullifying-hom-Group G N H f K g) =
  comp-hom-Group G H K g (hom-nullifying-hom-Group G H N f)
pr2 (precomp-nullifying-hom-Group G N H f K g) h p =
  ( inv (preserves-unit-hom-Group H K g)) ∙
  ( ap
    ( map-hom-Group H K g)
    ( nullifies-normal-subgroup-nullifying-hom-Group G H N f h p))

universal-property-quotient-Group :
  {l1 l2 l3 : Level} (G : Group l1)
  (N : Normal-Subgroup l2 G) (Q : Group l3)
  (q : nullifying-hom-Group G Q N) → UUω
universal-property-quotient-Group G N Q q =
  {l : Level} (H : Group l) → is-equiv (precomp-nullifying-hom-Group G N Q q H)
```

### The quotient group

#### The quotient map and the underlying set of the quotient group

The underlying [set](foundation-core.sets.md) of the quotient group is defined
as the [set quotient](foundation.set-quotients.md) of the
[equivalence relation](foundation.equivalence-relations.md) induced by the
normal subgroup `N` of `G`. By this construction we immediately obtain the
quotient map `q : G → G/N`, which will be
[surjective](foundation.surjective-maps.md) and
[effective](foundation.effective-maps-equivalence-relations.md). This means that
the quotient group satisfies the condition

```text
  x⁻¹y ∈ N ↔ q x ＝ q y.
```

We will conclude later that this implies that the quotient map nullifies the
normal subgroup `N`.

```agda
module _
  {l1 l2 : Level} (G : Group l1) (N : Normal-Subgroup l2 G)
  where

  set-quotient-Group : Set (l1 ⊔ l2)
  set-quotient-Group =
    quotient-Set (equivalence-relation-congruence-Normal-Subgroup G N)

  type-quotient-Group : UU (l1 ⊔ l2)
  type-quotient-Group =
    set-quotient (equivalence-relation-congruence-Normal-Subgroup G N)

  is-set-type-quotient-Group : is-set type-quotient-Group
  is-set-type-quotient-Group =
    is-set-set-quotient (equivalence-relation-congruence-Normal-Subgroup G N)

  map-quotient-hom-Group : type-Group G → type-quotient-Group
  map-quotient-hom-Group =
    quotient-map (equivalence-relation-congruence-Normal-Subgroup G N)

  is-surjective-map-quotient-hom-Group :
    is-surjective map-quotient-hom-Group
  is-surjective-map-quotient-hom-Group =
    is-surjective-quotient-map
      ( equivalence-relation-congruence-Normal-Subgroup G N)

  is-effective-map-quotient-hom-Group :
    is-effective
      ( equivalence-relation-congruence-Normal-Subgroup G N)
      ( map-quotient-hom-Group)
  is-effective-map-quotient-hom-Group =
    is-effective-quotient-map
      ( equivalence-relation-congruence-Normal-Subgroup G N)

  abstract
    apply-effectiveness-map-quotient-hom-Group :
      {x y : type-Group G} →
      map-quotient-hom-Group x ＝ map-quotient-hom-Group y →
      sim-congruence-Normal-Subgroup G N x y
    apply-effectiveness-map-quotient-hom-Group =
      apply-effectiveness-quotient-map
        ( equivalence-relation-congruence-Normal-Subgroup G N)

  abstract
    apply-effectiveness-map-quotient-hom-Group' :
      {x y : type-Group G} →
      sim-congruence-Normal-Subgroup G N x y →
      map-quotient-hom-Group x ＝ map-quotient-hom-Group y
    apply-effectiveness-map-quotient-hom-Group' =
      apply-effectiveness-quotient-map'
        ( equivalence-relation-congruence-Normal-Subgroup G N)

  reflecting-map-quotient-hom-Group :
    reflecting-map-equivalence-relation
      ( equivalence-relation-congruence-Normal-Subgroup G N)
      ( type-quotient-Group)
  reflecting-map-quotient-hom-Group =
    reflecting-map-quotient-map
      ( equivalence-relation-congruence-Normal-Subgroup G N)

  is-set-quotient-set-quotient-Group :
    is-set-quotient
      ( equivalence-relation-congruence-Normal-Subgroup G N)
      ( set-quotient-Group)
      ( reflecting-map-quotient-hom-Group)
  is-set-quotient-set-quotient-Group =
    is-set-quotient-set-quotient
      ( equivalence-relation-congruence-Normal-Subgroup G N)
```

#### The group structure on the quotient group

We now introduce the group structure on the underlying set of the quotient
group. The multiplication, unit, and inverses are defined by the universal
property of the set quotient as the unique maps equipped with identifications

```text
  (qx)(qy) ＝ q(xy)
         1 ＝ q1
    (qx)⁻¹ ＝ q(x⁻¹)
```

The group laws follow by the induction principle for set quotients.

```agda
module _
  {l1 l2 : Level} (G : Group l1) (N : Normal-Subgroup l2 G)
  where

  unit-quotient-Group : type-quotient-Group G N
  unit-quotient-Group = map-quotient-hom-Group G N (unit-Group G)

  binary-hom-mul-quotient-Group :
    binary-hom-equivalence-relation
      ( equivalence-relation-congruence-Normal-Subgroup G N)
      ( equivalence-relation-congruence-Normal-Subgroup G N)
      ( equivalence-relation-congruence-Normal-Subgroup G N)
  pr1 binary-hom-mul-quotient-Group = mul-Group G
  pr2 binary-hom-mul-quotient-Group =
    mul-congruence-Normal-Subgroup G N

  mul-quotient-Group :
    (x y : type-quotient-Group G N) → type-quotient-Group G N
  mul-quotient-Group =
    binary-map-set-quotient
      ( equivalence-relation-congruence-Normal-Subgroup G N)
      ( equivalence-relation-congruence-Normal-Subgroup G N)
      ( equivalence-relation-congruence-Normal-Subgroup G N)
      ( binary-hom-mul-quotient-Group)

  mul-quotient-Group' :
    (x y : type-quotient-Group G N) → type-quotient-Group G N
  mul-quotient-Group' x y = mul-quotient-Group y x

  abstract
    compute-mul-quotient-Group :
      (x y : type-Group G) →
      mul-quotient-Group
        ( map-quotient-hom-Group G N x)
        ( map-quotient-hom-Group G N y) ＝
      map-quotient-hom-Group G N (mul-Group G x y)
    compute-mul-quotient-Group =
      compute-binary-map-set-quotient
        ( equivalence-relation-congruence-Normal-Subgroup G N)
        ( equivalence-relation-congruence-Normal-Subgroup G N)
        ( equivalence-relation-congruence-Normal-Subgroup G N)
        ( binary-hom-mul-quotient-Group)

  hom-inv-quotient-Group :
    hom-equivalence-relation
      ( equivalence-relation-congruence-Normal-Subgroup G N)
      ( equivalence-relation-congruence-Normal-Subgroup G N)
  pr1 hom-inv-quotient-Group = inv-Group G
  pr2 hom-inv-quotient-Group = inv-congruence-Normal-Subgroup G N

  inv-quotient-Group : type-quotient-Group G N → type-quotient-Group G N
  inv-quotient-Group =
    map-set-quotient
      ( equivalence-relation-congruence-Normal-Subgroup G N)
      ( equivalence-relation-congruence-Normal-Subgroup G N)
      ( hom-inv-quotient-Group)

  abstract
    compute-inv-quotient-Group :
      (x : type-Group G) →
      inv-quotient-Group (map-quotient-hom-Group G N x) ＝
      map-quotient-hom-Group G N (inv-Group G x)
    compute-inv-quotient-Group =
      coherence-square-map-set-quotient
        ( equivalence-relation-congruence-Normal-Subgroup G N)
        ( equivalence-relation-congruence-Normal-Subgroup G N)
        ( hom-inv-quotient-Group)

  abstract
    left-unit-law-mul-quotient-Group :
      (x : type-quotient-Group G N) →
      mul-quotient-Group unit-quotient-Group x ＝ x
    left-unit-law-mul-quotient-Group =
      induction-set-quotient
        ( equivalence-relation-congruence-Normal-Subgroup G N)
        ( λ y →
          Id-Prop
            ( set-quotient-Group G N)
            ( mul-quotient-Group unit-quotient-Group y)
            ( y))
        ( λ x →
          ( compute-mul-quotient-Group (unit-Group G) x) ∙
          ( ap (map-quotient-hom-Group G N) (left-unit-law-mul-Group G x)))

  abstract
    right-unit-law-mul-quotient-Group :
      (x : type-quotient-Group G N) →
      mul-quotient-Group x unit-quotient-Group ＝ x
    right-unit-law-mul-quotient-Group =
      induction-set-quotient
        ( equivalence-relation-congruence-Normal-Subgroup G N)
        ( λ y →
          Id-Prop
            ( set-quotient-Group G N)
            ( mul-quotient-Group y unit-quotient-Group)
            ( y))
        ( λ x →
          ( compute-mul-quotient-Group x (unit-Group G)) ∙
          ( ap (map-quotient-hom-Group G N) (right-unit-law-mul-Group G x)))

  abstract
    associative-mul-quotient-Group :
      (x y z : type-quotient-Group G N) →
      ( mul-quotient-Group (mul-quotient-Group x y) z) ＝
      ( mul-quotient-Group x (mul-quotient-Group y z))
    associative-mul-quotient-Group =
      triple-induction-set-quotient'
        ( equivalence-relation-congruence-Normal-Subgroup G N)
        ( λ x y z →
          Id-Prop
            ( set-quotient-Group G N)
            ( mul-quotient-Group (mul-quotient-Group x y) z)
            ( mul-quotient-Group x (mul-quotient-Group y z)))
        ( λ x y z →
          ( ap
            ( mul-quotient-Group' (map-quotient-hom-Group G N z))
            ( compute-mul-quotient-Group x y)) ∙
          ( compute-mul-quotient-Group (mul-Group G x y) z) ∙
          ( ap
            ( map-quotient-hom-Group G N)
            ( associative-mul-Group G x y z)) ∙
          ( inv (compute-mul-quotient-Group x (mul-Group G y z))) ∙
          ( ap
            ( mul-quotient-Group (map-quotient-hom-Group G N x))
            ( inv (compute-mul-quotient-Group y z))))

  abstract
    left-inverse-law-mul-quotient-Group :
      (x : type-quotient-Group G N) →
      ( mul-quotient-Group (inv-quotient-Group x) x) ＝
      ( unit-quotient-Group)
    left-inverse-law-mul-quotient-Group =
      induction-set-quotient
        ( equivalence-relation-congruence-Normal-Subgroup G N)
        ( λ y →
          Id-Prop
            ( set-quotient-Group G N)
            ( mul-quotient-Group (inv-quotient-Group y) y)
            ( unit-quotient-Group))
        ( λ x →
          ( ap
            ( mul-quotient-Group' (map-quotient-hom-Group G N x))
            ( compute-inv-quotient-Group x)) ∙
          ( compute-mul-quotient-Group (inv-Group G x) x) ∙
          ( ap
            ( map-quotient-hom-Group G N)
            ( left-inverse-law-mul-Group G x)))

  abstract
    right-inverse-law-mul-quotient-Group :
      (x : type-quotient-Group G N) →
      ( mul-quotient-Group x (inv-quotient-Group x)) ＝
      ( unit-quotient-Group)
    right-inverse-law-mul-quotient-Group =
      induction-set-quotient
        ( equivalence-relation-congruence-Normal-Subgroup G N)
        ( λ y →
          Id-Prop
            ( set-quotient-Group G N)
            ( mul-quotient-Group y (inv-quotient-Group y))
            ( unit-quotient-Group))
        ( λ x →
          ( ap
            ( mul-quotient-Group (map-quotient-hom-Group G N x))
            ( compute-inv-quotient-Group x)) ∙
          ( compute-mul-quotient-Group x (inv-Group G x)) ∙
          ( ap
            ( map-quotient-hom-Group G N)
            ( right-inverse-law-mul-Group G x)))

  semigroup-quotient-Group : Semigroup (l1 ⊔ l2)
  pr1 semigroup-quotient-Group = set-quotient-Group G N
  pr1 (pr2 semigroup-quotient-Group) = mul-quotient-Group
  pr2 (pr2 semigroup-quotient-Group) = associative-mul-quotient-Group

  quotient-Group : Group (l1 ⊔ l2)
  pr1 quotient-Group = semigroup-quotient-Group
  pr1 (pr1 (pr2 quotient-Group)) = unit-quotient-Group
  pr1 (pr2 (pr1 (pr2 quotient-Group))) = left-unit-law-mul-quotient-Group
  pr2 (pr2 (pr1 (pr2 quotient-Group))) = right-unit-law-mul-quotient-Group
  pr1 (pr2 (pr2 quotient-Group)) = inv-quotient-Group
  pr1 (pr2 (pr2 (pr2 quotient-Group))) = left-inverse-law-mul-quotient-Group
  pr2 (pr2 (pr2 (pr2 quotient-Group))) = right-inverse-law-mul-quotient-Group
```

#### The quotient homomorphism into the quotient group

The quotient map `q : G → G/N` preserves the group structure and nullifies the
normal subgroup `N`. Both these claims follow fairly directly from the
definitions of the quotient map `q` and the group operations on `G/N`.

```agda
module _
  {l1 l2 : Level} (G : Group l1) (N : Normal-Subgroup l2 G)
  where

  abstract
    preserves-mul-quotient-hom-Group :
      preserves-mul-Group G
        ( quotient-Group G N)
        ( map-quotient-hom-Group G N)
    preserves-mul-quotient-hom-Group =
      inv (compute-mul-quotient-Group G N _ _)

  preserves-unit-quotient-hom-Group :
    map-quotient-hom-Group G N (unit-Group G) ＝ unit-quotient-Group G N
  preserves-unit-quotient-hom-Group = refl

  abstract
    preserves-inv-quotient-hom-Group :
      (x : type-Group G) →
      map-quotient-hom-Group G N (inv-Group G x) ＝
      inv-quotient-Group G N (map-quotient-hom-Group G N x)
    preserves-inv-quotient-hom-Group x =
      inv (compute-inv-quotient-Group G N x)

  quotient-hom-Group : hom-Group G (quotient-Group G N)
  pr1 quotient-hom-Group = map-quotient-hom-Group G N
  pr2 quotient-hom-Group = preserves-mul-quotient-hom-Group

  nullifies-normal-subgroup-quotient-hom-Group :
    nullifies-normal-subgroup-hom-Group G
      ( quotient-Group G N)
      ( quotient-hom-Group)
      ( N)
  nullifies-normal-subgroup-quotient-hom-Group x n =
    inv
      ( apply-effectiveness-map-quotient-hom-Group' G N
        ( unit-congruence-Normal-Subgroup' G N n))

  nullifying-quotient-hom-Group : nullifying-hom-Group G (quotient-Group G N) N
  pr1 nullifying-quotient-hom-Group = quotient-hom-Group
  pr2 nullifying-quotient-hom-Group =
    nullifies-normal-subgroup-quotient-hom-Group
```

#### Induction on quotient groups

The **induction principle** of quotient groups asserts that for any property `P`
of elements of the quotient group `G/N`, in order to show that `P x` holds for
all `x : G/N` it suffices to show that `P qy` holds for all `y : G`.

```agda
module _
  {l1 l2 l3 : Level} (G : Group l1) (N : Normal-Subgroup l2 G)
  (P : type-quotient-Group G N → Prop l3)
  where

  equiv-induction-quotient-Group :
    ((x : type-quotient-Group G N) → type-Prop (P x)) ≃
    ((x : type-Group G) → type-Prop (P (map-quotient-hom-Group G N x)))
  equiv-induction-quotient-Group =
    equiv-induction-set-quotient
      ( equivalence-relation-congruence-Normal-Subgroup G N)
      ( P)

  abstract
    induction-quotient-Group :
      ((x : type-Group G) → type-Prop (P (map-quotient-hom-Group G N x))) →
      ((x : type-quotient-Group G N) → type-Prop (P x))
    induction-quotient-Group =
      induction-set-quotient
        ( equivalence-relation-congruence-Normal-Subgroup G N)
        ( P)
```

#### Double induction on quotient groups

The **double induction principle** of quotient groups asserts that for any
property `P` of pairs of elements of the quotient group `G/N`, in order to show
that `P x y` holds for all `x y : G/N` it suffices to show that `P qu qv` holds
for all `u v : G`.

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (G : Group l1) (H : Group l2)
  (N : Normal-Subgroup l3 G) (M : Normal-Subgroup l4 H)
  (P : type-quotient-Group G N → type-quotient-Group H M → Prop l5)
  where

  equiv-double-induction-quotient-Group :
    ( (x : type-quotient-Group G N) (y : type-quotient-Group H M) →
      type-Prop (P x y)) ≃
    ( (x : type-Group G) (y : type-Group H) →
      type-Prop
        ( P (map-quotient-hom-Group G N x) (map-quotient-hom-Group H M y)))
  equiv-double-induction-quotient-Group =
    equiv-double-induction-set-quotient
      ( equivalence-relation-congruence-Normal-Subgroup G N)
      ( equivalence-relation-congruence-Normal-Subgroup H M)
      ( P)

  abstract
    double-induction-quotient-Group :
      ( (x : type-Group G) (y : type-Group H) →
        type-Prop
          ( P (map-quotient-hom-Group G N x) (map-quotient-hom-Group H M y))) →
      ( (x : type-quotient-Group G N) (y : type-quotient-Group H M) →
        type-Prop (P x y))
    double-induction-quotient-Group =
      double-induction-set-quotient
        ( equivalence-relation-congruence-Normal-Subgroup G N)
        ( equivalence-relation-congruence-Normal-Subgroup H M)
        ( P)
```

#### The universal property of the quotient group

The universal property of the quotient group `G/N` asserts that for any group
`H` the precomposition function

```text
  hom-Group G/N H → nullifying-hom-Group G H N
```

is an equivalence.

**Proof:** Let `G` and `H` be groups and let `N` be a normal subgroup of `G`.
Our goal is to show that the precomposition function

```text
  hom-Group G/N H → nullifying-hom-Group G H N
```

is an equivalence. To see this, note that the above map is a composite of the
maps

```text
  hom-Group G/N H → Σ (reflecting-map G H) (λ u → preserves-mul (pr1 u))
                  ≃ Σ (hom-Group G H) (λ f → is-nullifying f)
```

The second map is the equivalence `compute-nullifying-hom-Group` constructed
above. The first map is an equivalence by the universal property of set
quotients, by which we have:

```text
  (G/N → H) ≃ reflecting-map G H. ∎
```

```agda
module _
  {l1 l2 : Level} (G : Group l1) (N : Normal-Subgroup l2 G)
  where

  top-triangle-is-quotient-group-quotient-Group :
    {l : Level} (H : Group l) →
    hom-Group (quotient-Group G N) H →
    Σ ( reflecting-map-equivalence-relation
        ( equivalence-relation-congruence-Normal-Subgroup G N)
        ( type-Group H))
      ( λ f → preserves-mul-Group G H (pr1 f))
  top-triangle-is-quotient-group-quotient-Group H =
    map-Σ
      ( λ f → preserves-mul-Group G H (pr1 f))
      ( precomp-Set-Quotient
        ( equivalence-relation-congruence-Normal-Subgroup G N)
        ( set-quotient-Group G N)
        ( reflecting-map-quotient-map
          ( equivalence-relation-congruence-Normal-Subgroup G N))
        ( set-Group H))
      ( λ f μ →
        preserves-mul-comp-hom-Group G
          ( quotient-Group G N)
          ( H)
          ( f , μ)
          ( quotient-hom-Group G N))

  triangle-is-quotient-group-quotient-Group :
    {l : Level} (H : Group l) →
    coherence-triangle-maps
      ( precomp-nullifying-hom-Group G N
        ( quotient-Group G N)
        ( nullifying-quotient-hom-Group G N)
        ( H))
      ( map-equiv (compute-nullifying-hom-Group G H N))
      ( top-triangle-is-quotient-group-quotient-Group H)
  triangle-is-quotient-group-quotient-Group H x =
    eq-type-subtype
      ( λ f → nullifies-normal-subgroup-prop-hom-Group G H f N)
      ( refl)

  abstract
    is-equiv-top-triangle-is-quotient-group-quotient-Group :
      {l : Level} (H : Group l) →
      is-equiv (top-triangle-is-quotient-group-quotient-Group H)
    is-equiv-top-triangle-is-quotient-group-quotient-Group H =
      is-equiv-map-Σ
        ( λ f → preserves-mul-Group G H (pr1 f))
        ( is-set-quotient-set-quotient
          ( equivalence-relation-congruence-Normal-Subgroup G N)
          ( set-Group H))
        ( λ f →
          is-equiv-has-converse-is-prop
            ( is-prop-preserves-mul-Group (quotient-Group G N) H f)
            ( is-prop-preserves-mul-Group G H
              ( f ∘ map-quotient-hom-Group G N))
            ( λ μ {a} {b} →
              double-induction-quotient-Group G G N N
                ( λ x y → Id-Prop (set-Group H) _ _)
                ( λ x y → ap f (compute-mul-quotient-Group G N x y) ∙ μ)
                ( a)
                ( b)))

  abstract
    is-quotient-group-quotient-Group :
      universal-property-quotient-Group G N
        ( quotient-Group G N)
        ( nullifying-quotient-hom-Group G N)
    is-quotient-group-quotient-Group H =
      is-equiv-left-map-triangle
        ( precomp-nullifying-hom-Group G N
          ( quotient-Group G N)
          ( nullifying-quotient-hom-Group G N)
          ( H))
        ( map-equiv (compute-nullifying-hom-Group G H N))
        ( top-triangle-is-quotient-group-quotient-Group H)
        ( triangle-is-quotient-group-quotient-Group H)
        ( is-equiv-top-triangle-is-quotient-group-quotient-Group H)
        ( is-equiv-map-equiv (compute-nullifying-hom-Group G H N))
```

### The unique mapping property of the quotient group

The unique mapping property of the quotient group `G/N` asserts that for any
group `H` and any `N`-nullifying group homomorphism `f : G → H`, the type of
group homomorphisms `g : G/N → H` such that `f ~ g ∘ q` is
[contractible](foundation-core.contractible-types.md). In other words, it
asserts that any nullifying group homomorphism `f : G → H` extends uniquely
along `q`:

```text
     G
    | \
  q |  \ f
    |   \
    ∨    ∨
   G/N -> H.
       ∃!
```

```agda
module _
  {l1 l2 l3 : Level} (G : Group l1) (N : Normal-Subgroup l2 G)
  (H : Group l3)
  where

  abstract
    unique-mapping-property-quotient-Group :
      (f : nullifying-hom-Group G H N) →
      is-contr
        ( Σ ( hom-Group (quotient-Group G N) H)
            ( λ g →
              htpy-hom-Group G H
                ( hom-nullifying-hom-Group G H N
                  ( precomp-nullifying-hom-Group G N
                    ( quotient-Group G N)
                    ( nullifying-quotient-hom-Group G N)
                    ( H)
                    ( g)))
                ( hom-nullifying-hom-Group G H N f)))
    unique-mapping-property-quotient-Group f =
      is-contr-equiv' _
        ( equiv-tot
          ( λ g →
            ( extensionality-hom-Group G H _ _) ∘e
            ( extensionality-type-subtype'
              ( λ h → nullifies-normal-subgroup-prop-hom-Group G H h N)
              ( _)
              ( _))))
        ( is-contr-map-is-equiv
          ( is-quotient-group-quotient-Group G N H)
          ( f))

  abstract
    hom-universal-property-quotient-Group :
      (f : hom-Group G H)
      (n : nullifies-normal-subgroup-hom-Group G H f N) →
      hom-Group (quotient-Group G N) H
    hom-universal-property-quotient-Group f n =
      pr1 (center (unique-mapping-property-quotient-Group (f , n)))

    compute-hom-universal-property-quotient-Group :
      (f : hom-Group G H)
      (n : nullifies-normal-subgroup-hom-Group G H f N) →
      htpy-hom-Group G H
        ( hom-nullifying-hom-Group G H N
          ( precomp-nullifying-hom-Group G N
            ( quotient-Group G N)
            ( nullifying-quotient-hom-Group G N)
            ( H)
            ( hom-universal-property-quotient-Group f n)))
        ( hom-nullifying-hom-Group G H N (f , n))
    compute-hom-universal-property-quotient-Group f n =
      pr2 (center (unique-mapping-property-quotient-Group (f , n)))
```

## Properties

### An element is in a normal subgroup `N` if and only if it is in the kernel of the quotient group homomorphism `G → G/N`

```agda
module _
  {l1 l2 : Level} (G : Group l1) (N : Normal-Subgroup l2 G)
  where

  abstract
    is-in-kernel-quotient-hom-is-in-Normal-Subgroup :
      {x : type-Group G} → is-in-Normal-Subgroup G N x →
      is-in-kernel-hom-Group G (quotient-Group G N) (quotient-hom-Group G N) x
    is-in-kernel-quotient-hom-is-in-Normal-Subgroup =
      nullifies-normal-subgroup-quotient-hom-Group G N _

  abstract
    is-in-normal-subgroup-is-in-kernel-quotient-hom-Group :
      {x : type-Group G} →
      is-in-kernel-hom-Group G (quotient-Group G N) (quotient-hom-Group G N) x →
      is-in-Normal-Subgroup G N x
    is-in-normal-subgroup-is-in-kernel-quotient-hom-Group {x} H =
      unit-congruence-Normal-Subgroup G N
        ( apply-effectiveness-map-quotient-hom-Group G N (inv H))
```

## External links

- [Fundamental theorem on homomorphisms](https://en.wikipedia.org/wiki/Fundamental_theorem_on_homomorphisms)
  on Wikipedia
