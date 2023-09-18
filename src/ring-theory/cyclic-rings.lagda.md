# Cyclic rings

```agda
{-# OPTIONS --allow-unsolved-metas #-}

module ring-theory.cyclic-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.ring-of-integers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.fibers-of-maps
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
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

A [ring](ring-theory.rings.md) is said to be **cyclic** if its underlying
additive [group](group-theory.groups.md) is a
[cyclic group](group-theory.cyclic-groups.md).

Since rings in the agda-unimath library are assumed to be unital by default, it
follows that cyclic rings come equipped with a
[generating element](group-theory.generating-elements-groups.md). Indeed, the
unit element is a generating element of any cyclic ring.

Note that the classification of cyclic unital rings is somewhat different from
the nonunital cyclic rings: Cyclic unital rings are
[quotients](ring-theory.quotient-rings.md) of the
[ring `ℤ` of integers](elementary-number-theory.ring-of-integers.md), whereas
cyclic nonunital rings are isomorphic to [ideals](ring-theory.ideals-rings.md)
of quotients of the ring `ℤ` \[1\].

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
```

## Properties

### If `R` is a cyclic ring, then any generator of its additive group is invertible

**Proof:** Let `g` be a generator of the additive group `(R,0,+,-)`. Then there
is an integer `k` such that `kg ＝ 1`. Then we obtain that
`(k1)g ＝ k(1g) ＝ kg ＝ 1` and that `g(k1) ＝ k(g1) ＝ kg ＝ 1`. It follows
that the element `k1` is the multiplicative inverse of `g`.

```agda
module _
  {l : Level} (R : Ring l) (g : type-Ring R)
  (H : is-generating-element-Group (group-Ring R) g)
  where

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
      ( λ (k , p) →
        ( map-initial-hom-Ring R k) ,
        ( ( right-integer-multiple-law-mul-Ring R k g (one-Ring R)) ∙
          ( ap (integer-multiple-Ring R k) (right-unit-law-mul-Ring R g)) ∙
          ( p)) ,
        ( ( left-integer-multiple-law-mul-Ring R k (one-Ring R) g) ∙
          ( ap (integer-multiple-Ring R k) (left-unit-law-mul-Ring R g)) ∙
          ( p)))
```

### If `R` is a cyclic ring, then any invertible element is a generator of its additive group

Let `x` be an invertible element of `R` and let `g` be a generating element of
the additive group `(R,0,+,-)`. Then there exist integers `k` and `l` such that
`kg ＝ x` and `lg ＝ x⁻¹`. Now we see that
`lx ＝ lkg ＝ klg ＝ kx⁻¹. Therefore we obtain that `lk1 ＝ lk(xx⁻1) ＝ lxkx⁻¹

```agda
module _
  {l : Level} (R : Cyclic-Ring l)
  where

  is-generating-element-group-is-invertible-element-Cyclic-Ring :
    (x : type-Cyclic-Ring R) →
    is-invertible-element-Ring (ring-Cyclic-Ring R) x →
    is-generating-element-Group (group-Cyclic-Ring R) x
  is-generating-element-group-is-invertible-element-Cyclic-Ring x H =
    apply-universal-property-trunc-Prop
      ( is-cyclic-Cyclic-Ring R)
      ( is-generating-element-prop-Group (group-Cyclic-Ring R) x)
      ( λ (g , G) →
        apply-twice-universal-property-trunc-Prop
          ( is-surjective-hom-element-is-generating-element-Group
            ( group-Cyclic-Ring R)
            ( g)
            ( G)
            ( x))
          ( is-surjective-hom-element-is-generating-element-Group
            ( group-Cyclic-Ring R)
            ( g)
            ( G)
            ( pr1 H))
          ( is-generating-element-prop-Group (group-Cyclic-Ring R) x)
          ( λ { (k , refl) (l , q) →
                is-generating-element-is-surjective-hom-element-Group
                  ( group-Cyclic-Ring R)
                  ( _)
                  ( λ y →
                    apply-universal-property-trunc-Prop
                      ( is-surjective-hom-element-is-generating-element-Group
                        ( group-Cyclic-Ring R)
                        ( g)
                        ( G)
                        ( y))
                      ( trunc-Prop
                        ( fiber
                          ( map-hom-element-Group (group-Cyclic-Ring R) _)
                          ( y)))
                      ( λ { (n , refl) →
                            unit-trunc-Prop
                              ( ( mul-ℤ n l) ,
                                ( {!!}))}))}))
```

### If `R` is a cyclic ring, then `1` is a generator of its additive group

To do

### `R` is a cylcic ring if and only if `initial-hom-Ring R` is surjective

```agda
module _
  {l : Level} (R : Cyclic-Ring l)
  where

  is-surjective-initial-hom-Cyclic-Ring :
    is-surjective (map-initial-hom-Ring (ring-Cyclic-Ring R))
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
            ( x))
          ( trunc-Prop
            ( fiber (map-initial-hom-Ring (ring-Cyclic-Ring R)) x))
          ( λ { (k , p) (l , refl) →
                unit-trunc-Prop
                  {!!}}))

  is-generating-element-one-Cyclic-Ring :
    is-generating-element-Group (group-Cyclic-Ring R) (one-Cyclic-Ring R)
  is-generating-element-one-Cyclic-Ring x =
    apply-universal-property-trunc-Prop
      ( is-cyclic-Cyclic-Ring R)
      ( trunc-Prop (Σ {!ℤ!} {!!}))
      {!!}

  commutative-mul-Cyclic-Ring :
    (x y : type-Cyclic-Ring R) →
    mul-Cyclic-Ring R x y ＝ mul-Cyclic-Ring R y x
  commutative-mul-Cyclic-Ring x y =
    apply-universal-property-trunc-Prop
      ( is-cyclic-Cyclic-Ring R)
      ( Id-Prop (set-Cyclic-Ring R) _ _)
      ( λ (g , u) →
        {!!})
```

## References

- \[1\] Maria Balintne-Szendrei, Gabor Czedli, and Agnes Szendrei. _Absztrakt
  algebrai feladatok (Exercises in Abstract Algebra)_. Polygon, Szeged, 2005.
