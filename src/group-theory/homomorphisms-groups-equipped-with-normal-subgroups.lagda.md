# Homomorphisms of groups equipped with normal subgroups

```agda
open import foundation.function-extensionality-axiom

module
  group-theory.homomorphisms-groups-equipped-with-normal-subgroups
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-types funext
open import foundation.identity-types funext
open import foundation.subtypes funext
open import foundation.universe-levels

open import group-theory.groups funext
open import group-theory.homomorphisms-groups funext
open import group-theory.normal-subgroups funext
open import group-theory.pullbacks-subgroups funext
open import group-theory.subgroups funext
```

</details>

## Idea

Consider a [group](group-theory.groups.md) `G` equipped with a
[normal subgroup](group-theory.normal-subgroups.md) and a group `H` equipped
with a normal subgroup `M`. A **homomorphism of groups equipped with normal
subgroups** from `(G,N)` to `(H,M)` consists of a
[group homomorphism](group-theory.homomorphisms-groups.md) `f : G → H` which
**reflects** the normal subgroup `N` into `M`, i.e., such that the condition
`x ∈ N ⇒ f x ∈ M` holds.

## Definitions

### The property of group homomorphisms of reflecting a normal subgroup

We say that a group homomorphism `f : G → H` **reflects** a normal subgroup `N`
of `G` into a normal subgroup `M` of `H` if the property

```text
  x ∈ N ⇒ f x ∈ M
```

holds for every `x : G`, i.e., if `f` maps elements in `N` to elements in `M`.

## Definitions

### The predicate of reflecting a normal subgroup

```agda
module _
  {l1 l2 l3 l4 : Level} (G : Group l1) (H : Group l2)
  (N : Normal-Subgroup l3 G) (M : Normal-Subgroup l4 H)
  where

  reflects-normal-subgroup-hom-Group : hom-Group G H → UU (l1 ⊔ l3 ⊔ l4)
  reflects-normal-subgroup-hom-Group f =
    leq-Normal-Subgroup G N (pullback-Normal-Subgroup G H f M)

  reflecting-hom-Group : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  reflecting-hom-Group = Σ (hom-Group G H) reflects-normal-subgroup-hom-Group
```

### Reflecting group homomorphisms

```agda
module _
  {l1 l2 l3 l4 : Level} (G : Group l1) (H : Group l2)
  (N : Normal-Subgroup l3 G) (M : Normal-Subgroup l4 H)
  (f : reflecting-hom-Group G H N M)
  where

  hom-reflecting-hom-Group : hom-Group G H
  hom-reflecting-hom-Group = pr1 f

  reflects-normal-subgroup-reflecting-hom-Group :
    reflects-normal-subgroup-hom-Group G H N M hom-reflecting-hom-Group
  reflects-normal-subgroup-reflecting-hom-Group = pr2 f

  map-reflecting-hom-Group : type-Group G → type-Group H
  map-reflecting-hom-Group = map-hom-Group G H hom-reflecting-hom-Group
```

### The identity reflecting group homomorphism

We define two variations of the identity reflecting group homomorphism. We will
define the standard identity reflecting group homomorphism, but we will also we
define a generalized version which takes as an argument an arbitrary element of

```text
  reflects-normal-subgroup-hom-Group G G N N (id-hom-Group G).
```

The purpose is that in functoriality proofs, the proof that the identity
homomorphism is reflecting is not always the standard one.

```agda
module _
  {l1 l2 : Level} (G : Group l1) (N : Normal-Subgroup l2 G)
  where

  reflects-normal-subgroup-id-hom-Group :
    reflects-normal-subgroup-hom-Group G G N N (id-hom-Group G)
  reflects-normal-subgroup-id-hom-Group =
    refl-leq-subtype (subset-Normal-Subgroup G N)

  id-reflecting-hom-Group' :
    (p : reflects-normal-subgroup-hom-Group G G N N (id-hom-Group G)) →
    reflecting-hom-Group G G N N
  pr1 (id-reflecting-hom-Group' p) = id-hom-Group G
  pr2 (id-reflecting-hom-Group' p) = p

  id-reflecting-hom-Group : reflecting-hom-Group G G N N
  id-reflecting-hom-Group =
    id-reflecting-hom-Group' reflects-normal-subgroup-id-hom-Group
```

### Composition of reflecting group homomorphisms

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (G : Group l1) (H : Group l2) (K : Group l3)
  (L : Normal-Subgroup l4 G) (M : Normal-Subgroup l5 H)
  (N : Normal-Subgroup l6 K)
  where

  hom-comp-reflecting-hom-Group :
    reflecting-hom-Group H K M N →
    reflecting-hom-Group G H L M →
    hom-Group G K
  hom-comp-reflecting-hom-Group g f =
    comp-hom-Group G H K
      ( hom-reflecting-hom-Group H K M N g)
      ( hom-reflecting-hom-Group G H L M f)

  map-comp-reflecting-hom-Group :
    reflecting-hom-Group H K M N →
    reflecting-hom-Group G H L M →
    type-Group G → type-Group K
  map-comp-reflecting-hom-Group g f =
    map-hom-Group G K (hom-comp-reflecting-hom-Group g f)

  reflects-normal-subgroup-comp-reflecting-hom-Group :
    (g : reflecting-hom-Group H K M N) →
    (f : reflecting-hom-Group G H L M) →
    reflects-normal-subgroup-hom-Group G K L N
      ( hom-comp-reflecting-hom-Group g f)
  reflects-normal-subgroup-comp-reflecting-hom-Group g f =
    transitive-leq-subtype
      ( subset-Normal-Subgroup G L)
      ( subset-Normal-Subgroup H M ∘ map-reflecting-hom-Group G H L M f)
      ( subset-Normal-Subgroup K N ∘ map-comp-reflecting-hom-Group g f)
      ( ( reflects-normal-subgroup-reflecting-hom-Group H K M N g) ∘
        ( map-reflecting-hom-Group G H L M f))
      ( reflects-normal-subgroup-reflecting-hom-Group G H L M f)

  comp-reflecting-hom-Group' :
    (g : reflecting-hom-Group H K M N) (f : reflecting-hom-Group G H L M) →
    (p :
      reflects-normal-subgroup-hom-Group G K L N
        ( hom-comp-reflecting-hom-Group g f)) →
    reflecting-hom-Group G K L N
  pr1 (comp-reflecting-hom-Group' g f p) = hom-comp-reflecting-hom-Group g f
  pr2 (comp-reflecting-hom-Group' g f p) = p

  comp-reflecting-hom-Group :
    reflecting-hom-Group H K M N →
    reflecting-hom-Group G H L M →
    reflecting-hom-Group G K L N
  comp-reflecting-hom-Group g f =
    comp-reflecting-hom-Group' g f
      ( reflects-normal-subgroup-comp-reflecting-hom-Group g f)
```

### Homotopies of reflecting homomorphisms

```agda
module _
  {l1 l2 l3 l4 : Level}
  (G : Group l1) (H : Group l2)
  (N : Normal-Subgroup l3 G) (M : Normal-Subgroup l4 H)
  where

  htpy-reflecting-hom-Group :
    reflecting-hom-Group G H N M → reflecting-hom-Group G H N M → UU (l1 ⊔ l2)
  htpy-reflecting-hom-Group f g =
    htpy-hom-Group G H
      ( hom-reflecting-hom-Group G H N M f)
      ( hom-reflecting-hom-Group G H N M g)

  refl-htpy-reflecting-hom-Group :
    (f : reflecting-hom-Group G H N M) → htpy-reflecting-hom-Group f f
  refl-htpy-reflecting-hom-Group f =
    refl-htpy-hom-Group G H (hom-reflecting-hom-Group G H N M f)
```

## Properties

### Characterization of equality of reflecting homomorphisms

```agda
module _
  {l1 l2 l3 l4 : Level}
  (G : Group l1) (H : Group l2)
  (N : Normal-Subgroup l3 G) (M : Normal-Subgroup l4 H)
  (f : reflecting-hom-Group G H N M)
  where

  htpy-eq-reflecting-hom-Group :
    (g : reflecting-hom-Group G H N M) →
    f ＝ g → htpy-reflecting-hom-Group G H N M f g
  htpy-eq-reflecting-hom-Group g refl =
    refl-htpy-reflecting-hom-Group G H N M f
```
