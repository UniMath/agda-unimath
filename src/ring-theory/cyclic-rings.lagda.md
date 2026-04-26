# Cyclic rings

```agda
module ring-theory.cyclic-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.ring-of-integers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.surjective-maps
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.cyclic-groups
open import group-theory.free-groups-with-one-generator
open import group-theory.generating-elements-groups
open import group-theory.groups

open import ring-theory.integer-multiples-of-elements-rings
open import ring-theory.invertible-elements-rings
open import ring-theory.rings
```

</details>

## Idea

A [ring](ring-theory.rings.md) is said to be
{{#concept "cyclic" Disambiguation="ring" Agda=Cyclic-Ring}} if its underlying
additive [group](group-theory.groups.md) is a
[cyclic group](group-theory.cyclic-groups.md). We will show that the following
three claims about a ring `R` are equivalent:

1. The ring `R` is cyclic.
2. The element `1` is a
   [generating element](group-theory.generating-elements-groups.md) of the
   [abelian group](group-theory.abelian-groups.md) `(R,0,+,-)`.
3. The [subset](foundation.subtypes.md) of generating elements of `R` is the
   subset of [invertible elements](ring-theory.invertible-elements-rings.md) of
   `R`.

Cyclic rings therefore have a specified generating element, i.e., the element
`1`. With this fact in the pocket, it is easy to show that cyclic rings are
[commutative rings](commutative-algebra.commutative-rings.md). Furthermore, the
multiplicative structure of `R` coincides with the multiplicative structure
constructed in
[`group-theory.generating-elements-groups`](group-theory.generating-elements-groups.md)
using the generating element `1`. In particular, it follows that for any cyclic
group `G`, the type of ring structures on `G` is equivalent with the type of
generating elements of `G`.

Note that the classification of cyclic unital rings is somewhat different from
the nonunital cyclic rings: Cyclic unital rings are
[quotients](ring-theory.quotient-rings.md) of the
[ring `ℤ` of integers](elementary-number-theory.ring-of-integers.md), whereas
cyclic nonunital rings are isomorphic to [ideals](ring-theory.ideals-rings.md)
of quotients of the ring `ℤ`. {{#cite BSCS05}}

Since cyclic rings are quotients of `ℤ`, it follows that quotients of cyclic
rings are cyclic rings.

## Definitions

### The predicate of being a cyclic ring

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-cyclic-prop-Ring : Prop l
  is-cyclic-prop-Ring = is-cyclic-prop-Group (group-Ring R)

  is-cyclic-Ring : UU l
  is-cyclic-Ring = is-cyclic-Group (group-Ring R)

  is-prop-is-cyclic-Ring : is-prop is-cyclic-Ring
  is-prop-is-cyclic-Ring = is-prop-is-cyclic-Group (group-Ring R)
```

### The predicate of the initial morphism being surjective

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-surjective-initial-hom-prop-Ring : Prop l
  is-surjective-initial-hom-prop-Ring =
    is-surjective-Prop (map-initial-hom-Ring R)

  is-surjective-initial-hom-Ring : UU l
  is-surjective-initial-hom-Ring =
    type-Prop is-surjective-initial-hom-prop-Ring

  is-prop-is-surjective-initial-hom-Ring :
    is-prop is-surjective-initial-hom-Ring
  is-prop-is-surjective-initial-hom-Ring =
    is-prop-type-Prop is-surjective-initial-hom-prop-Ring
```

### Cyclic rings

```agda
Cyclic-Ring : (l : Level) → UU (lsuc l)
Cyclic-Ring l = Σ (Ring l) is-cyclic-Ring

module _
  {l : Level} (R : Cyclic-Ring l)
  where

  ring-Cyclic-Ring : Ring l
  ring-Cyclic-Ring = pr1 R

  ab-Cyclic-Ring : Ab l
  ab-Cyclic-Ring = ab-Ring ring-Cyclic-Ring

  group-Cyclic-Ring : Group l
  group-Cyclic-Ring = group-Ring ring-Cyclic-Ring

  is-cyclic-Cyclic-Ring : is-cyclic-Ring ring-Cyclic-Ring
  is-cyclic-Cyclic-Ring = pr2 R

  cyclic-group-Cyclic-Ring : Cyclic-Group l
  pr1 cyclic-group-Cyclic-Ring = group-Cyclic-Ring
  pr2 cyclic-group-Cyclic-Ring = is-cyclic-Cyclic-Ring

  type-Cyclic-Ring : UU l
  type-Cyclic-Ring = type-Ring ring-Cyclic-Ring

  set-Cyclic-Ring : Set l
  set-Cyclic-Ring = set-Ring ring-Cyclic-Ring

  zero-Cyclic-Ring : type-Cyclic-Ring
  zero-Cyclic-Ring = zero-Ring ring-Cyclic-Ring

  one-Cyclic-Ring : type-Cyclic-Ring
  one-Cyclic-Ring = one-Ring ring-Cyclic-Ring

  add-Cyclic-Ring : (x y : type-Cyclic-Ring) → type-Cyclic-Ring
  add-Cyclic-Ring = add-Ring ring-Cyclic-Ring

  neg-Cyclic-Ring : type-Cyclic-Ring → type-Cyclic-Ring
  neg-Cyclic-Ring = neg-Ring ring-Cyclic-Ring

  mul-Cyclic-Ring : (x y : type-Cyclic-Ring) → type-Cyclic-Ring
  mul-Cyclic-Ring = mul-Ring ring-Cyclic-Ring

  mul-Cyclic-Ring' : (x y : type-Cyclic-Ring) → type-Cyclic-Ring
  mul-Cyclic-Ring' = mul-Ring' ring-Cyclic-Ring

  integer-multiple-Cyclic-Ring : ℤ → type-Cyclic-Ring → type-Cyclic-Ring
  integer-multiple-Cyclic-Ring = integer-multiple-Ring ring-Cyclic-Ring

  left-unit-law-add-Cyclic-Ring :
    (x : type-Cyclic-Ring) →
    add-Cyclic-Ring zero-Cyclic-Ring x ＝ x
  left-unit-law-add-Cyclic-Ring =
    left-unit-law-add-Ring ring-Cyclic-Ring

  right-unit-law-add-Cyclic-Ring :
    (x : type-Cyclic-Ring) →
    add-Cyclic-Ring x zero-Cyclic-Ring ＝ x
  right-unit-law-add-Cyclic-Ring =
    right-unit-law-add-Ring ring-Cyclic-Ring

  associative-add-Cyclic-Ring :
    (x y z : type-Cyclic-Ring) →
    add-Cyclic-Ring (add-Cyclic-Ring x y) z ＝
    add-Cyclic-Ring x (add-Cyclic-Ring y z)
  associative-add-Cyclic-Ring =
    associative-add-Ring ring-Cyclic-Ring

  left-inverse-law-add-Cyclic-Ring :
    (x : type-Cyclic-Ring) →
    add-Cyclic-Ring (neg-Cyclic-Ring x) x ＝ zero-Cyclic-Ring
  left-inverse-law-add-Cyclic-Ring =
    left-inverse-law-add-Ring ring-Cyclic-Ring

  right-inverse-law-add-Cyclic-Ring :
    (x : type-Cyclic-Ring) →
    add-Cyclic-Ring x (neg-Cyclic-Ring x) ＝ zero-Cyclic-Ring
  right-inverse-law-add-Cyclic-Ring =
    right-inverse-law-add-Ring ring-Cyclic-Ring

  left-unit-law-mul-Cyclic-Ring :
    (x : type-Cyclic-Ring) →
    mul-Cyclic-Ring one-Cyclic-Ring x ＝ x
  left-unit-law-mul-Cyclic-Ring =
    left-unit-law-mul-Ring ring-Cyclic-Ring

  right-unit-law-mul-Cyclic-Ring :
    (x : type-Cyclic-Ring) →
    mul-Cyclic-Ring x one-Cyclic-Ring ＝ x
  right-unit-law-mul-Cyclic-Ring =
    right-unit-law-mul-Ring ring-Cyclic-Ring

  associative-mul-Cyclic-Ring :
    (x y z : type-Cyclic-Ring) →
    mul-Cyclic-Ring (mul-Cyclic-Ring x y) z ＝
    mul-Cyclic-Ring x (mul-Cyclic-Ring y z)
  associative-mul-Cyclic-Ring =
    associative-mul-Ring ring-Cyclic-Ring

  left-distributive-mul-add-Cyclic-Ring :
    (x y z : type-Cyclic-Ring) →
    mul-Cyclic-Ring x (add-Cyclic-Ring y z) ＝
    add-Cyclic-Ring (mul-Cyclic-Ring x y) (mul-Cyclic-Ring x z)
  left-distributive-mul-add-Cyclic-Ring =
    left-distributive-mul-add-Ring ring-Cyclic-Ring

  right-distributive-mul-add-Cyclic-Ring :
    (x y z : type-Cyclic-Ring) →
    mul-Cyclic-Ring (add-Cyclic-Ring x y) z ＝
    add-Cyclic-Ring (mul-Cyclic-Ring x z) (mul-Cyclic-Ring y z)
  right-distributive-mul-add-Cyclic-Ring =
    right-distributive-mul-add-Ring ring-Cyclic-Ring

  swap-integer-multiple-Cyclic-Ring :
    (k l : ℤ) (x : type-Cyclic-Ring) →
    integer-multiple-Cyclic-Ring k (integer-multiple-Cyclic-Ring l x) ＝
    integer-multiple-Cyclic-Ring l (integer-multiple-Cyclic-Ring k x)
  swap-integer-multiple-Cyclic-Ring =
    swap-integer-multiple-Ring ring-Cyclic-Ring

  left-integer-multiple-law-mul-Cyclic-Ring :
    (k : ℤ) (x y : type-Cyclic-Ring) →
    mul-Cyclic-Ring (integer-multiple-Cyclic-Ring k x) y ＝
    integer-multiple-Cyclic-Ring k (mul-Cyclic-Ring x y)
  left-integer-multiple-law-mul-Cyclic-Ring =
    left-integer-multiple-law-mul-Ring ring-Cyclic-Ring

  right-integer-multiple-law-mul-Cyclic-Ring :
    (k : ℤ) (x y : type-Cyclic-Ring) →
    mul-Cyclic-Ring x (integer-multiple-Cyclic-Ring k y) ＝
    integer-multiple-Cyclic-Ring k (mul-Cyclic-Ring x y)
  right-integer-multiple-law-mul-Cyclic-Ring =
    right-integer-multiple-law-mul-Ring ring-Cyclic-Ring
```

## Properties

### If `R` is a cyclic ring, then any generator of its additive group is invertible

**Proof:** Let `g` be a generator of the additive group `(R,0,+,-)`. Then there
is an integer `n` such that `ng ＝ 1`. Then we obtain that
`(n1)g ＝ n(1g) ＝ ng ＝ 1` and that `g(n1) ＝ n(g1) ＝ ng ＝ 1`. It follows
that the element `n1` is the multiplicative inverse of `g`.

```agda
module _
  {l : Level} (R : Ring l) (g : type-Ring R)
  (H : is-generating-element-Group (group-Ring R) g)
  where

  abstract
    is-invertible-is-generating-element-group-Ring :
      is-invertible-element-Ring R g
    is-invertible-is-generating-element-group-Ring =
      apply-universal-property-trunc-Prop
        ( is-surjective-hom-element-is-generating-element-Group
          ( group-Ring R)
          ( g)
          ( H)
          ( one-Ring R))
        ( is-invertible-element-prop-Ring R g)
        ( λ (n , p) →
          ( integer-multiple-Ring R n (one-Ring R)) ,
          ( ( right-integer-multiple-law-mul-Ring R n g
              ( one-Ring R)) ∙
            ( ap
              ( integer-multiple-Ring R n)
              ( right-unit-law-mul-Ring R g)) ∙
            ( p)) ,
          ( ( left-integer-multiple-law-mul-Ring R n
              ( one-Ring R)
              ( g)) ∙
            ( ap
              ( integer-multiple-Ring R n)
              ( left-unit-law-mul-Ring R g)) ∙
            ( p)))
```

### If `R` is a cyclic ring if and only if `1` is a generator of its additive group

Equivalently, we assert that `R` is cyclic if and only if `initial-hom-Ring R`
is surjective.

**Proof:** Of course, if `1` is a generator of the additive group of `R`, then
the additive group of `R` is cyclic. For the converse, consider a generating
element `g` of the additive group `(R,0,+,-)`. Then there exists an integer `n`
such that `ng ＝ 1`.

Let `x` be an arbitrary element of the ring `R`. Then there exists an integer
`k` such that `kg ＝ gx`. We claim that `k1 ＝ x`. To see this, we calculate:

```text
  k1 ＝ k(ng) ＝ n(kg) ＝ n(gx) ＝ (ng)x ＝ 1x ＝ x.
```

This proves that every element is an integer multiple of `1`. We conclude that
`1` generates the additive group `(R,0,+,-)`.

```agda
module _
  {l : Level} (R : Cyclic-Ring l)
  where

  abstract
    is-surjective-initial-hom-Cyclic-Ring :
      is-surjective-initial-hom-Ring (ring-Cyclic-Ring R)
    is-surjective-initial-hom-Cyclic-Ring x =
      apply-universal-property-trunc-Prop
        ( is-cyclic-Cyclic-Ring R)
        ( trunc-Prop
          ( fiber (map-initial-hom-Ring (ring-Cyclic-Ring R)) x))
        ( λ (g , u) →
          apply-twice-universal-property-trunc-Prop
            ( is-surjective-hom-element-is-generating-element-Group
              ( group-Cyclic-Ring R)
              ( g)
              ( u)
              ( one-Cyclic-Ring R))
            ( is-surjective-hom-element-is-generating-element-Group
              ( group-Cyclic-Ring R)
              ( g)
              ( u)
              ( mul-Cyclic-Ring R g x))
            ( trunc-Prop
              ( fiber (map-initial-hom-Ring (ring-Cyclic-Ring R)) x))
            ( λ (n , p) (k , q) →
              unit-trunc-Prop
                ( ( k) ,
                  ( equational-reasoning
                    integer-multiple-Cyclic-Ring R k
                      ( one-Cyclic-Ring R)
                    ＝ integer-multiple-Cyclic-Ring R k
                        ( integer-multiple-Cyclic-Ring R n g)
                      by
                      ap
                        ( integer-multiple-Cyclic-Ring R k)
                        ( inv p)
                    ＝ integer-multiple-Cyclic-Ring R n
                        ( integer-multiple-Cyclic-Ring R k g)
                      by
                      swap-integer-multiple-Cyclic-Ring R k n g
                    ＝ integer-multiple-Cyclic-Ring R n
                        ( mul-Cyclic-Ring R g x)
                      by
                      ap (integer-multiple-Cyclic-Ring R n) q
                    ＝ mul-Cyclic-Ring R
                        ( integer-multiple-Cyclic-Ring R n g)
                        ( x)
                      by
                      inv (left-integer-multiple-law-mul-Cyclic-Ring R n g x)
                    ＝ mul-Cyclic-Ring R (one-Cyclic-Ring R) x
                      by ap (mul-Cyclic-Ring' R x) p
                    ＝ x
                      by left-unit-law-mul-Cyclic-Ring R x))))

  abstract
    is-generating-element-one-Cyclic-Ring :
      is-generating-element-Group (group-Cyclic-Ring R) (one-Cyclic-Ring R)
    is-generating-element-one-Cyclic-Ring =
      is-generating-element-is-surjective-hom-element-Group
        ( group-Cyclic-Ring R)
        ( one-Cyclic-Ring R)
        ( is-surjective-initial-hom-Cyclic-Ring)
```

### The classification of cyclic rings

```agda
module _
  {l : Level}
  where

  is-cyclic-is-surjective-initial-hom-Ring :
    (R : Ring l) →
    is-surjective-initial-hom-Ring R → is-cyclic-Ring R
  is-cyclic-is-surjective-initial-hom-Ring R H =
    unit-trunc-Prop
      ( one-Ring R ,
        is-generating-element-is-surjective-hom-element-Group
          ( group-Ring R)
          ( one-Ring R)
          ( H))

  classification-Cyclic-Ring :
    Cyclic-Ring l ≃ Σ (Ring l) is-surjective-initial-hom-Ring
  classification-Cyclic-Ring =
    equiv-type-subtype
      ( is-prop-is-cyclic-Ring)
      ( is-prop-is-surjective-initial-hom-Ring)
      ( λ R H → is-surjective-initial-hom-Cyclic-Ring (R , H))
      ( is-cyclic-is-surjective-initial-hom-Ring)
```

### If `R` is a cyclic ring, then any invertible element is a generator of its additive group

**Proof:** Let `x` be an invertible element of `R`. To show that `x` generates
the abelian group `(R,0,+,1)` we need to show that for any element `y : R` there
exists an integer `k` such that `kx ＝ y`. Let `n1 ＝ x⁻¹` and let `m1 ＝ y`.
Then we calculate

```text
  (mn)x ＝ m(nx) ＝ m(n(1x)) ＝ m((n1)x) ＝ m(x⁻¹x) ＝ m1 ＝ y.
```

```agda
module _
  {l : Level} (R : Cyclic-Ring l) {x : type-Cyclic-Ring R}
  (H : is-invertible-element-Ring (ring-Cyclic-Ring R) x)
  where

  abstract
    is-surjective-hom-element-is-invertible-element-Cyclic-Ring :
      is-surjective-hom-element-Group (group-Cyclic-Ring R) x
    is-surjective-hom-element-is-invertible-element-Cyclic-Ring y =
      apply-twice-universal-property-trunc-Prop
        ( is-surjective-initial-hom-Cyclic-Ring R
          ( inv-is-invertible-element-Ring (ring-Cyclic-Ring R) H))
        ( is-surjective-initial-hom-Cyclic-Ring R y)
        ( trunc-Prop (fiber (map-hom-element-Group (group-Cyclic-Ring R) x) y))
        ( λ (n , p) (m , q) →
          unit-trunc-Prop
            ( ( mul-ℤ m n) ,
              ( ( integer-multiple-mul-Ring (ring-Cyclic-Ring R) m n x) ∙
                ( ap
                  ( integer-multiple-Cyclic-Ring R m)
                  ( ( ap
                      ( integer-multiple-Cyclic-Ring R n)
                      ( inv (left-unit-law-mul-Cyclic-Ring R x))) ∙
                    ( inv
                      ( left-integer-multiple-law-mul-Ring
                        ( ring-Cyclic-Ring R)
                        ( n)
                        ( one-Cyclic-Ring R)
                        ( x))) ∙
                    ( ap (mul-Cyclic-Ring' R x) p) ∙
                    ( is-left-inverse-inv-is-invertible-element-Ring
                      ( ring-Cyclic-Ring R)
                      ( H)))) ∙
                ( q))))

  is-generating-element-group-is-invertible-element-Cyclic-Ring :
    is-generating-element-Group (group-Cyclic-Ring R) x
  is-generating-element-group-is-invertible-element-Cyclic-Ring =
    is-generating-element-is-surjective-hom-element-Group
      ( group-Cyclic-Ring R)
      ( x)
      ( is-surjective-hom-element-is-invertible-element-Cyclic-Ring)
```

### Any cyclic ring is commutative

```agda
module _
  {l : Level} (R : Cyclic-Ring l)
  where

  abstract
    commutative-mul-Cyclic-Ring :
      (x y : type-Cyclic-Ring R) →
      mul-Cyclic-Ring R x y ＝ mul-Cyclic-Ring R y x
    commutative-mul-Cyclic-Ring x y =
      apply-twice-universal-property-trunc-Prop
        ( is-surjective-initial-hom-Cyclic-Ring R x)
        ( is-surjective-initial-hom-Cyclic-Ring R y)
        ( Id-Prop (set-Cyclic-Ring R) _ _)
        ( λ where
          ( n , refl) (m , refl) →
            commute-integer-multiples-diagonal-Ring (ring-Cyclic-Ring R) n m)

  commutative-ring-Cyclic-Ring : Commutative-Ring l
  pr1 commutative-ring-Cyclic-Ring = ring-Cyclic-Ring R
  pr2 commutative-ring-Cyclic-Ring = commutative-mul-Cyclic-Ring
```

## See also

### Table of files related to cyclic types, groups, and rings

{{#include tables/cyclic-types.md}}

## References

{{#bibliography}}
