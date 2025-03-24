# Normalizer subgroups

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module group-theory.normalizer-subgroups
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions funext
open import foundation.equality-dependent-pair-types funext
open import foundation.functoriality-dependent-pair-types funext
open import foundation.identity-types funext
open import foundation.logical-equivalences funext
open import foundation.propositions funext univalence
open import foundation.subtypes funext univalence truncations
open import foundation.universe-levels

open import group-theory.conjugation funext univalence truncations
open import group-theory.groups funext univalence truncations
open import group-theory.homomorphisms-groups funext univalence truncations
open import group-theory.subgroups funext univalence truncations
open import group-theory.subsets-groups funext univalence truncations
```

</details>

## Idea

Consider a [subgroup](group-theory.subgroups.md) `H` of a
[group](group-theory.groups.md) `G`. The **normalizer subgroup** `Nᴳ(H)` of `G`
is the largest subgroup of `G` of which `H` is a
[normal subgroup](group-theory.normal-subgroups.md). The normalizer subgroup
consists of all elements `g : G` such that `h ∈ H ⇔ (gh)g⁻¹ ∈ H` for all
`h ∈ G`. In other words, the normalizer subgroup consists of all elements `g`
such that `(gH)g⁻¹ ＝ H`.

The weaker condition that `(gH)g⁻¹ ⊆ H` is
[not sufficient](https://math.stackexchange.com/q/107862) in the case of
infinite groups. In this case, the group elements satisfying this weaker
condition may not be closed under inverses.

Note: The normalizer subgroup should not be confused with the
[normal closure](group-theory.normal-closures-subgroups.md) of a subgroup, or
with the [normal core](group-theory.normal-cores-subgroups.md) of a subgroup.

## Definitions

### The universal property of the normalizer subgroup

```agda
module _
  {l1 l2 l3 : Level} (G : Group l1) (H : Subgroup l2 G)
  (N : Subgroup l3 G)
  where

  is-normalizer-Subgroup : UUω
  is-normalizer-Subgroup =
    {l : Level} (K : Subgroup l G) →
    ( {x y : type-Group G} →
      is-in-Subgroup G K x →
      is-in-Subgroup G H y →
      is-in-Subgroup G H (conjugation-Group G x y)) ↔
    leq-Subgroup G K N
```

### The construction of the normalizer subgroup

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Subgroup l2 G)
  where

  subset-normalizer-Subgroup : subset-Group (l1 ⊔ l2) G
  subset-normalizer-Subgroup x =
    implicit-Π-Prop
      ( type-Group G)
      ( λ y →
        iff-Prop
          ( subset-Subgroup G H y)
          ( subset-Subgroup G H (conjugation-Group G x y)))

  is-in-normalizer-Subgroup : type-Group G → UU (l1 ⊔ l2)
  is-in-normalizer-Subgroup =
    is-in-subtype subset-normalizer-Subgroup

  is-closed-under-eq-normalizer-Subgroup :
    {x y : type-Group G} →
    is-in-normalizer-Subgroup x → x ＝ y → is-in-normalizer-Subgroup y
  is-closed-under-eq-normalizer-Subgroup =
    is-closed-under-eq-subtype subset-normalizer-Subgroup

  restrict-conjugation-Subgroup :
    (x : type-Group G) → is-in-normalizer-Subgroup x →
    type-Subgroup G H → type-Subgroup G H
  pr1 (restrict-conjugation-Subgroup x u (y , h)) = conjugation-Group G x y
  pr2 (restrict-conjugation-Subgroup x u (y , h)) = forward-implication u h

  contains-unit-normalizer-Subgroup :
    contains-unit-subset-Group G subset-normalizer-Subgroup
  pr1 contains-unit-normalizer-Subgroup u =
    is-closed-under-eq-Subgroup' G H u (compute-conjugation-unit-Group G _)
  pr2 contains-unit-normalizer-Subgroup u =
    is-closed-under-eq-Subgroup G H u (compute-conjugation-unit-Group G _)

  is-closed-under-multiplication-normalizer-Subgroup :
    is-closed-under-multiplication-subset-Group G subset-normalizer-Subgroup
  pr1 (is-closed-under-multiplication-normalizer-Subgroup {x} {y} u v) w =
    is-closed-under-eq-Subgroup' G H
      ( forward-implication u (forward-implication v w))
      ( compute-conjugation-mul-Group G x y _)
  pr2 (is-closed-under-multiplication-normalizer-Subgroup {x} {y} u v) w =
    backward-implication v
      ( backward-implication u
        ( is-closed-under-eq-Subgroup G H w
          ( compute-conjugation-mul-Group G x y _)))

  is-closed-under-inverses-normalizer-Subgroup :
    is-closed-under-inverses-subset-Group G subset-normalizer-Subgroup
  pr1 (is-closed-under-inverses-normalizer-Subgroup {x} u {y}) h =
    backward-implication u
      ( is-closed-under-eq-Subgroup' G H h
        ( is-section-conjugation-inv-Group G x y))
  pr2 (is-closed-under-inverses-normalizer-Subgroup {x} u {y}) h =
    is-closed-under-eq-Subgroup G H
      ( forward-implication u h)
      ( is-section-conjugation-inv-Group G x y)

  normalizer-Subgroup : Subgroup (l1 ⊔ l2) G
  pr1 normalizer-Subgroup =
    subset-normalizer-Subgroup
  pr1 (pr2 normalizer-Subgroup) =
    contains-unit-normalizer-Subgroup
  pr1 (pr2 (pr2 normalizer-Subgroup)) =
    is-closed-under-multiplication-normalizer-Subgroup
  pr2 (pr2 (pr2 normalizer-Subgroup)) =
    is-closed-under-inverses-normalizer-Subgroup

  forward-implication-is-normalizer-normalizer-Subgroup :
    {l : Level} (K : Subgroup l G) →
    ( {x y : type-Group G} → is-in-Subgroup G K x →
      is-in-Subgroup G H y →
      is-in-Subgroup G H (conjugation-Group G x y)) →
    leq-Subgroup G K normalizer-Subgroup
  pr1 (forward-implication-is-normalizer-normalizer-Subgroup K u x k {y}) h =
    u k h
  pr2 (forward-implication-is-normalizer-normalizer-Subgroup K u x k {y}) h =
    is-closed-under-eq-Subgroup G H
      ( u (is-closed-under-inverses-Subgroup G K {x} k) h)
      ( is-retraction-conjugation-inv-Group G x y)

  backward-implication-is-normalizer-normalizer-Subgroup :
    {l : Level} (K : Subgroup l G) → leq-Subgroup G K normalizer-Subgroup →
    {x y : type-Group G} → is-in-Subgroup G K x →
    is-in-Subgroup G H y →
    is-in-Subgroup G H (conjugation-Group G x y)
  backward-implication-is-normalizer-normalizer-Subgroup K u {x} {y} k h =
    forward-implication (u x k) h

  is-normalizer-normalizer-Subgroup :
    is-normalizer-Subgroup G H normalizer-Subgroup
  pr1 (is-normalizer-normalizer-Subgroup K) =
    forward-implication-is-normalizer-normalizer-Subgroup K
  pr2 (is-normalizer-normalizer-Subgroup K) =
    backward-implication-is-normalizer-normalizer-Subgroup K
```

### The inclusion of `H` into its normalizer `Nᴳ(H)`

```agda
module _
  {l1 l2 l3 : Level} (G : Group l1) (H : Subgroup l2 G) (N : Subgroup l3 G)
  (is-normalizer-G-H-N : is-normalizer-Subgroup G H N)
  where

  is-in-normalizer-is-in-type-Subgroup :
    (x : type-Group G) → is-in-Subgroup G H x → is-in-Subgroup G N x
  is-in-normalizer-is-in-type-Subgroup =
    forward-implication
      ( is-normalizer-G-H-N H)
      ( λ x' y' →
        is-closed-under-multiplication-Subgroup G H
          ( is-closed-under-multiplication-Subgroup G H x' y')
          ( is-closed-under-inverses-Subgroup G H x'))

  inclusion-is-normalizer-Subgroup : type-Subgroup G H → type-Subgroup G N
  inclusion-is-normalizer-Subgroup = tot is-in-normalizer-is-in-type-Subgroup

  hom-inclusion-is-normalizer-Subgroup :
    hom-Group (group-Subgroup G H) (group-Subgroup G N)
  pr1 hom-inclusion-is-normalizer-Subgroup =
    inclusion-is-normalizer-Subgroup
  pr2 hom-inclusion-is-normalizer-Subgroup =
    eq-type-subtype (subset-Subgroup G N) refl
```

## See also

- [Centralizer subgroups](group-theory.centralizer-subgroups.md)
- [Normal closures of subgroups](group-theory.normal-closures-subgroups.md)
- [Normal cores of subgroups](group-theory.normal-cores-subgroups.md)

## External links

- [normalizer](https://ncatlab.org/nlab/show/normalizer) at $n$Lab
- [Centralizer and normalizer](https://en.wikipedia.org/wiki/Centralizer_and_normalizer)
  at Wikipedia
- [Normalizer of a subgroup](https://groupprops.subwiki.org/wiki/Normalizer_of_a_subgroup)
  at Groupprops
