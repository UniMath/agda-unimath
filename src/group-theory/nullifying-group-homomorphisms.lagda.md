# Nullifying group homomorphisms

```agda
module group-theory.nullifying-group-homomorphisms where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.propositions
open import foundation.reflecting-maps-equivalence-relations
open import foundation.subtypes
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import group-theory.groups
open import group-theory.homomorphisms-groups
open import group-theory.homomorphisms-groups-equipped-with-normal-subgroups
open import group-theory.kernels-homomorphisms-groups
open import group-theory.normal-subgroups
```

</details>

## Idea

Consider a [group homomorphism](group-theory.homomorphisms-groups.md)
`f : G → H` and a [normal subgroup](group-theory.normal-subgroups.md) `N` of the
[group](group-theory.groups.md) `G`. We say that `f` **nullifies** `N` if it
satisfies the condition

```text
  N ⊆ ker f,
```

i.e., if `f x ＝ 1` for all `x ∈ N`. Nullifying group homomorphisms are used to
define [quotient groups](group-theory.quotient-groups.md).

## Definitions

### The predicate of nullifying a normal subgroup

```agda
module _
  {l1 l2 l3 : Level} (G : Group l1) (K : Group l2)
  where

  nullifies-normal-subgroup-prop-hom-Group :
    hom-Group G K → Normal-Subgroup l3 G → Prop (l1 ⊔ l2 ⊔ l3)
  nullifies-normal-subgroup-prop-hom-Group f H =
    leq-prop-Normal-Subgroup G H (kernel-hom-Group G K f)

  nullifies-normal-subgroup-hom-Group :
    hom-Group G K → Normal-Subgroup l3 G → UU (l1 ⊔ l2 ⊔ l3)
  nullifies-normal-subgroup-hom-Group f H =
    type-Prop (nullifies-normal-subgroup-prop-hom-Group f H)
```

### Group homomorphisms that nullify a normal subgroup, i.e., that contain a normal subgroup in their kernel

```agda
module _
  {l1 l2 l3 : Level} (G : Group l1) (K : Group l2) (H : Normal-Subgroup l3 G)
  where

  nullifying-hom-Group : UU (l1 ⊔ l2 ⊔ l3)
  nullifying-hom-Group =
    type-subtype (λ f → nullifies-normal-subgroup-prop-hom-Group G K f H)

  hom-nullifying-hom-Group :
    nullifying-hom-Group → hom-Group G K
  hom-nullifying-hom-Group = pr1

  nullifies-normal-subgroup-nullifying-hom-Group :
    (f : nullifying-hom-Group) →
    nullifies-normal-subgroup-hom-Group G K
      ( hom-nullifying-hom-Group f) H
  nullifies-normal-subgroup-nullifying-hom-Group = pr2
```

## Properties

### A group homomorphism nullifies a normal subgroup if and only if it reflects the equivalence relation induced by the normal subgroup

```agda
module _
  {l1 l2 l3 : Level} (G : Group l1) (K : Group l2)
  (H : Normal-Subgroup l3 G)
  where

  reflects-equivalence-relation-nullifies-normal-subgroup-hom-Group :
    (f : hom-Group G K) →
    nullifies-normal-subgroup-hom-Group G K f H →
    reflects-equivalence-relation
      ( equivalence-relation-congruence-Normal-Subgroup G H)
      ( map-hom-Group G K f)
  reflects-equivalence-relation-nullifies-normal-subgroup-hom-Group f p α =
    ( inv (right-unit-law-mul-Group K _)) ∙
    ( inv-transpose-eq-mul-Group' K
      ( ( p (left-div-Group G _ _) α) ∙
        ( preserves-left-div-hom-Group G K f)))

  nullifies-normal-subgroup-reflects-equivalence-relation-hom-Group :
    (f : hom-Group G K) →
    reflects-equivalence-relation
      ( equivalence-relation-congruence-Normal-Subgroup G H)
      ( map-hom-Group G K f) →
    nullifies-normal-subgroup-hom-Group G K f H
  nullifies-normal-subgroup-reflects-equivalence-relation-hom-Group f p x q =
    ( inv (preserves-unit-hom-Group G K f)) ∙
    ( p ( is-closed-under-multiplication-Normal-Subgroup G H
          ( is-closed-under-inverses-Normal-Subgroup G H
            ( contains-unit-Normal-Subgroup G H))
          ( q)))

  compute-nullifying-hom-Group :
    Σ ( reflecting-map-equivalence-relation
        ( equivalence-relation-congruence-Normal-Subgroup G H)
        ( type-Group K))
      ( λ f → preserves-mul-Group G K (pr1 f)) ≃
    nullifying-hom-Group G K H
  compute-nullifying-hom-Group =
    ( equiv-type-subtype
      ( λ f →
        is-prop-reflects-equivalence-relation
          ( equivalence-relation-congruence-Normal-Subgroup G H)
          ( set-Group K)
          ( pr1 f))
      ( λ f → is-prop-leq-Normal-Subgroup G H (kernel-hom-Group G K f))
      ( nullifies-normal-subgroup-reflects-equivalence-relation-hom-Group)
      ( reflects-equivalence-relation-nullifies-normal-subgroup-hom-Group)) ∘e
    ( equiv-right-swap-Σ)
```

### Composition of nullifying homomorphisms and reflecting homomorphisms

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (G : Group l1) (H : Group l2) (K : Group l3)
  (N : Normal-Subgroup l4 G) (M : Normal-Subgroup l5 H)
  where

  hom-comp-nullifying-hom-reflecting-hom-Group :
    nullifying-hom-Group H K M →
    reflecting-hom-Group G H N M →
    hom-Group G K
  hom-comp-nullifying-hom-reflecting-hom-Group g f =
    comp-hom-Group G H K
      ( hom-nullifying-hom-Group H K M g)
      ( hom-reflecting-hom-Group G H N M f)

  nullifies-normal-subgroup-comp-nullifying-hom-reflecting-hom-Group :
    ( g : nullifying-hom-Group H K M)
    ( f : reflecting-hom-Group G H N M) →
    nullifies-normal-subgroup-hom-Group G K
      ( hom-comp-nullifying-hom-reflecting-hom-Group g f)
      ( N)
  nullifies-normal-subgroup-comp-nullifying-hom-reflecting-hom-Group g f x n =
    nullifies-normal-subgroup-nullifying-hom-Group H K M g
      ( map-reflecting-hom-Group G H N M f x)
      ( reflects-normal-subgroup-reflecting-hom-Group G H N M f x n)

  comp-nullifying-hom-reflecting-hom-Group :
    nullifying-hom-Group H K M →
    reflecting-hom-Group G H N M →
    nullifying-hom-Group G K N
  pr1 (comp-nullifying-hom-reflecting-hom-Group g f) =
    hom-comp-nullifying-hom-reflecting-hom-Group g f
  pr2 (comp-nullifying-hom-reflecting-hom-Group g f) =
    nullifies-normal-subgroup-comp-nullifying-hom-reflecting-hom-Group g f
```

## See also

- [Homomorphisms of groups equipped with normal subgroups](group-theory.homomorphisms-groups-equipped-with-normal-subgroups.md)
