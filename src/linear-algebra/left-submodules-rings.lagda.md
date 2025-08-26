# Left submodules over rings

```agda
module linear-algebra.left-submodules-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.intersections-subtypes
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import foundation-core.embeddings
open import foundation-core.equivalences
open import foundation-core.injective-maps
open import foundation-core.transport-along-identifications

open import group-theory.abelian-groups
open import group-theory.endomorphism-rings-abelian-groups
open import group-theory.groups
open import group-theory.homomorphisms-abelian-groups
open import group-theory.homomorphisms-semigroups
open import group-theory.monoids
open import group-theory.semigroups

open import linear-algebra.left-modules-rings
open import linear-algebra.subsets-left-modules-rings

open import ring-theory.homomorphisms-rings
open import ring-theory.rings
```

</details>

## Idea

A left submodule of a [left module](./left-modules-rings.lagda.md) `M` over a
[ring](../ring-theory/rings.lagda.md) `R` is a
[subset](./subsets-left-modules-rings.lagda.md) of `M` that is closed under
addition and multiplication by a scalar from `R`.

## Definitions

### Submodules over rings

```agda
module _
  {l1 l2 l3 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  (S : subset-left-module-Ring l3 R M)
  where

  is-left-submodule-Ring-prop : Prop (l1 ⊔ l2 ⊔ l3)
  is-left-submodule-Ring-prop =
    product-Prop
      ( contains-zero-prop-subset-left-module-Ring R M S)
      ( product-Prop
        ( is-closed-under-addition-prop-subset-left-module-Ring R M S)
        ( is-closed-under-multiplication-by-scalar-prop-subset-left-module-Ring
          R
          M
          S))

  is-left-submodule-Ring : UU (l1 ⊔ l2 ⊔ l3)
  is-left-submodule-Ring = type-Prop is-left-submodule-Ring-prop

left-submodule-Ring :
  {l1 l2 : Level}
  (l : Level) (R : Ring l1) (M : left-module-Ring l2 R) → UU (lsuc l ⊔ l1 ⊔ l2)
left-submodule-Ring l R M =
  type-subtype (is-left-submodule-Ring-prop {l3 = l} R M)
```

## Helper functions

```agda
module _
  {l1 l2 l3 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  (N : left-submodule-Ring l3 R M)
  where

  subset-left-submodule-Ring : subset-left-module-Ring l3 R M
  subset-left-submodule-Ring =
    inclusion-subtype (is-left-submodule-Ring-prop R M) N

  type-left-submodule-Ring : UU (l2 ⊔ l3)
  type-left-submodule-Ring = type-subtype subset-left-submodule-Ring

  inclusion-left-submodule-Ring :
    type-left-submodule-Ring → type-left-module-Ring R M
  inclusion-left-submodule-Ring =
    inclusion-subtype subset-left-submodule-Ring

  is-emb-inclusion-left-submodule-Ring :
    is-emb inclusion-left-submodule-Ring
  is-emb-inclusion-left-submodule-Ring =
    is-emb-inclusion-subtype subset-left-submodule-Ring

  eq-left-submodule-Ring-eq-left-module-Ring :
    is-injective (inclusion-left-submodule-Ring)
  eq-left-submodule-Ring-eq-left-module-Ring {x} {y} =
    map-inv-is-equiv (is-emb-inclusion-left-submodule-Ring x y)

  is-closed-under-addition-left-submodule-Ring :
    is-closed-under-addition-subset-left-module-Ring
      R
      M
      subset-left-submodule-Ring
  is-closed-under-addition-left-submodule-Ring = pr1 (pr2 (pr2 N))

  is-closed-under-multiplication-by-scalar-left-submodule-Ring :
    is-closed-under-multiplication-by-scalar-subset-left-module-Ring
      R
      M
      subset-left-submodule-Ring
  is-closed-under-multiplication-by-scalar-left-submodule-Ring =
    pr2 (pr2 (pr2 N))

  contains-zero-left-submodule-Ring :
    contains-zero-subset-left-module-Ring R M subset-left-submodule-Ring
  contains-zero-left-submodule-Ring = pr1 (pr2 N)

  unit-left-submodule-Ring : type-left-submodule-Ring
  pr1 unit-left-submodule-Ring = zero-left-module-Ring R M
  pr2 unit-left-submodule-Ring = contains-zero-left-submodule-Ring
```

## Properties

### The submodule is closed under negation

```agda
is-closed-under-negation-left-submodule-Ring :
  {l1 l2 l3 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  (N : left-submodule-Ring l3 R M) →
  is-closed-under-negation-subset-left-module-Ring
    R
    M
    ( subset-left-submodule-Ring R M N)
is-closed-under-negation-left-submodule-Ring R M N =
  λ x x-in-subset →
    tr
      ( λ x' → pr1 (subset-left-submodule-Ring R M N x'))
      ( mul-neg-one-left-module-Ring R M x)
      ( is-closed-under-multiplication-by-scalar-left-submodule-Ring
        R
        M
        N
        (neg-one-Ring R)
        x
        x-in-subset)
```

### The intersection of a family of submodules is a submodule

```agda
module _
  {l1 l2 l3 : Level} {I : UU l2}
  (R : Ring l1) (M : left-module-Ring l2 R) (F : I → left-submodule-Ring l3 R M)
  where

  subset-intersection-family-of-submodules :
    subset-left-module-Ring (l2 ⊔ l3) R M
  subset-intersection-family-of-submodules =
    intersection-family-of-subtypes (λ i → subset-left-submodule-Ring R M (F i))

  is-left-submodule-intersection-submodule-Ring :
    is-left-submodule-Ring R M subset-intersection-family-of-submodules
  pr1 is-left-submodule-intersection-submodule-Ring =
    λ i → contains-zero-left-submodule-Ring R M (F i)
  pr1 (pr2 is-left-submodule-intersection-submodule-Ring) =
    (λ x y x-in-subset y-in-subset i →
      (is-closed-under-addition-left-submodule-Ring R M (F i))
        x
        y
        (x-in-subset i)
        (y-in-subset i))
  pr2 (pr2 is-left-submodule-intersection-submodule-Ring) =
    (λ r x x-in-subset i →
      (is-closed-under-multiplication-by-scalar-left-submodule-Ring R M (F i))
        r
        x
        (x-in-subset i))
```

### A submodule has the structure of a module

```agda
module _
  {l1 l2 l3 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  (N : left-submodule-Ring l3 R M)
  where

  neg-left-submodule-Ring :
    type-left-submodule-Ring R M N → type-left-submodule-Ring R M N
  pr1 (neg-left-submodule-Ring x) = neg-left-module-Ring R M (pr1 x)
  pr2 (neg-left-submodule-Ring x) =
    is-closed-under-negation-left-submodule-Ring R M N (pr1 x) (pr2 x)

  add-left-submodule-Ring :
    (x y : type-left-submodule-Ring R M N) → type-left-submodule-Ring R M N
  pr1 (add-left-submodule-Ring x y) =
    add-left-module-Ring R M (pr1 x) (pr1 y)
  pr2 (add-left-submodule-Ring x y) =
    (is-closed-under-addition-left-submodule-Ring R M N)
      (pr1 x)
      (pr1 y)
      (pr2 x)
      (pr2 y)

  mul-left-submodule-Ring :
    (r : type-Ring R)
    (x : type-left-submodule-Ring R M N) →
    type-left-submodule-Ring R M N
  pr1 (mul-left-submodule-Ring r x) =
    mul-left-module-Ring R M r (pr1 x)
  pr2 (mul-left-submodule-Ring r x) =
    (is-closed-under-multiplication-by-scalar-left-submodule-Ring R M N)
      r
      (pr1 x)
      (pr2 x)

  associative-add-left-submodule-Ring :
    (x y z : type-left-submodule-Ring R M N) →
    Id
      (add-left-submodule-Ring (add-left-submodule-Ring x y) z)
      (add-left-submodule-Ring x (add-left-submodule-Ring y z))
  associative-add-left-submodule-Ring x y z =
    eq-left-submodule-Ring-eq-left-module-Ring
      R
      M
      N
      (associative-add-left-module-Ring R M (pr1 x) (pr1 y) (pr1 z))

  left-unit-law-add-left-submodule-Ring :
    (x : type-left-submodule-Ring R M N) →
    Id (add-left-submodule-Ring (unit-left-submodule-Ring R M N) x) x
  left-unit-law-add-left-submodule-Ring x =
    eq-left-submodule-Ring-eq-left-module-Ring
      R
      M
      N
      (left-unit-law-add-left-module-Ring R M (pr1 x))

  right-unit-law-add-left-submodule-Ring :
    (x : type-left-submodule-Ring R M N) →
    Id (add-left-submodule-Ring x (unit-left-submodule-Ring R M N)) x
  right-unit-law-add-left-submodule-Ring x =
    eq-left-submodule-Ring-eq-left-module-Ring
      R
      M
      N
      (right-unit-law-add-left-module-Ring R M (pr1 x))

  left-inverse-law-add-left-submodule-Ring :
    (x : type-left-submodule-Ring R M N) →
    Id
      (add-left-submodule-Ring (neg-left-submodule-Ring x) x)
      (unit-left-submodule-Ring R M N)
  left-inverse-law-add-left-submodule-Ring x =
    eq-left-submodule-Ring-eq-left-module-Ring
      R
      M
      N
      (left-inverse-law-add-left-module-Ring R M (pr1 x))

  right-inverse-law-add-left-submodule-Ring :
    (x : type-left-submodule-Ring R M N) →
    Id
      (add-left-submodule-Ring x (neg-left-submodule-Ring x))
      (unit-left-submodule-Ring R M N)
  right-inverse-law-add-left-submodule-Ring x =
    eq-left-submodule-Ring-eq-left-module-Ring
      R
      M
      N
      (right-inverse-law-add-left-module-Ring R M (pr1 x))

  add-commutative-left-submodule-Ring :
    (x y : type-left-submodule-Ring R M N) →
    Id (add-left-submodule-Ring x y) (add-left-submodule-Ring y x)
  add-commutative-left-submodule-Ring x y =
    eq-left-submodule-Ring-eq-left-module-Ring
      R M N (pr2 (pr1 M) (pr1 x) (pr1 y))

  left-distributive-law-left-submodule-Ring :
    (r : type-Ring R)
    (x y : type-left-submodule-Ring R M N) →
    Id
      (mul-left-submodule-Ring r (add-left-submodule-Ring x y))
      (add-left-submodule-Ring
        (mul-left-submodule-Ring r x)
        (mul-left-submodule-Ring r y))
  left-distributive-law-left-submodule-Ring r x y =
    eq-left-submodule-Ring-eq-left-module-Ring
      R
      M
      N
      (left-distributive-mul-add-left-module-Ring R M r (pr1 x) (pr1 y))

  right-distributive-law-left-submodule-Ring :
    (r s : type-Ring R)
    (x : type-left-submodule-Ring R M N) →
    Id
      (mul-left-submodule-Ring (add-Ring R r s) x)
      (add-left-submodule-Ring
        (mul-left-submodule-Ring r x)
        (mul-left-submodule-Ring s x))
  right-distributive-law-left-submodule-Ring r s x =
    eq-left-submodule-Ring-eq-left-module-Ring
      R
      M
      N
      (right-distributive-mul-add-left-module-Ring R M r s (pr1 x))

  associative-mul-left-submodule-Ring :
    (r s : type-Ring R)
    (x : type-left-submodule-Ring R M N) →
    Id
      (mul-left-submodule-Ring (mul-Ring R r s) x)
      (mul-left-submodule-Ring r (mul-left-submodule-Ring s x))
  associative-mul-left-submodule-Ring r s x =
    eq-left-submodule-Ring-eq-left-module-Ring
      R
      M
      N
      (associative-mul-left-module-Ring R M r s (pr1 x))

  left-unit-law-mul-left-submodule-Ring :
    (x : type-left-submodule-Ring R M N) →
    Id (mul-left-submodule-Ring (one-Ring R) x) x
  left-unit-law-mul-left-submodule-Ring x =
    eq-left-submodule-Ring-eq-left-module-Ring
      R
      M
      N
      (left-unit-law-mul-left-module-Ring R M (pr1 x))

  set-left-module-Ring-left-submodule-Ring : Set (l2 ⊔ l3)
  pr1 set-left-module-Ring-left-submodule-Ring =
    type-left-submodule-Ring R M N
  pr2 set-left-module-Ring-left-submodule-Ring =
    is-set-type-subtype
      (subset-left-submodule-Ring R M N)
      (is-set-type-left-module-Ring R M)

  semigroup-left-submodule-Ring : Semigroup (l2 ⊔ l3)
  pr1 semigroup-left-submodule-Ring = set-left-module-Ring-left-submodule-Ring
  pr1 (pr2 semigroup-left-submodule-Ring) = add-left-submodule-Ring
  pr2 (pr2 semigroup-left-submodule-Ring) = associative-add-left-submodule-Ring

  group-left-submodule-Ring : Group (l2 ⊔ l3)
  pr1 group-left-submodule-Ring = semigroup-left-submodule-Ring
  pr1 (pr1 (pr2 group-left-submodule-Ring)) = unit-left-submodule-Ring R M N
  pr1 (pr2 (pr1 (pr2 group-left-submodule-Ring))) =
    left-unit-law-add-left-submodule-Ring
  pr2 (pr2 (pr1 (pr2 group-left-submodule-Ring))) =
    right-unit-law-add-left-submodule-Ring
  pr1 (pr2 (pr2 group-left-submodule-Ring)) = neg-left-submodule-Ring
  pr1 (pr2 (pr2 (pr2 group-left-submodule-Ring))) =
    left-inverse-law-add-left-submodule-Ring
  pr2 (pr2 (pr2 (pr2 group-left-submodule-Ring))) =
    right-inverse-law-add-left-submodule-Ring

  ab-left-submodule-Ring : Ab (l2 ⊔ l3)
  pr1 ab-left-submodule-Ring = group-left-submodule-Ring
  pr2 ab-left-submodule-Ring = add-commutative-left-submodule-Ring

  endomorphism-ring-ab-left-submodule-Ring : Ring (l2 ⊔ l3)
  endomorphism-ring-ab-left-submodule-Ring =
    endomorphism-ring-Ab ab-left-submodule-Ring

  map-hom-left-submodule-Ring :
    (r : type-Ring R) → hom-Ab ab-left-submodule-Ring ab-left-submodule-Ring
  pr1 (map-hom-left-submodule-Ring r) = λ x → mul-left-submodule-Ring r x
  pr2 (map-hom-left-submodule-Ring r) {x} {y} =
    left-distributive-law-left-submodule-Ring r x y

  hom-Ring-left-submodule-Ring :
    hom-Ring R endomorphism-ring-ab-left-submodule-Ring
  pr1 (pr1 hom-Ring-left-submodule-Ring) = map-hom-left-submodule-Ring
  pr2 (pr1 hom-Ring-left-submodule-Ring) {r} {s} =
    eq-htpy-hom-Ab
      ab-left-submodule-Ring
      ab-left-submodule-Ring
      (right-distributive-law-left-submodule-Ring r s)
  pr1 (pr2 hom-Ring-left-submodule-Ring) {r} {s} =
    eq-htpy-hom-Ab
      ab-left-submodule-Ring
      ab-left-submodule-Ring
      (associative-mul-left-submodule-Ring r s)
  pr2 (pr2 hom-Ring-left-submodule-Ring) =
    eq-htpy-hom-Ab
      ab-left-submodule-Ring
      ab-left-submodule-Ring
      left-unit-law-mul-left-submodule-Ring

  module-left-submodule-Ring : left-module-Ring (l2 ⊔ l3) R
  pr1 module-left-submodule-Ring = ab-left-submodule-Ring
  pr2 module-left-submodule-Ring = hom-Ring-left-submodule-Ring
```
