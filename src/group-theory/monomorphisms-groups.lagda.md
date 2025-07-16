# Monomorphisms in the category of groups

```agda
{-# OPTIONS --lossy-unification #-}

module group-theory.monomorphisms-groups where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategories
open import category-theory.monomorphisms-in-large-precategories

open import elementary-number-theory.group-of-integers
open import elementary-number-theory.integers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.universe-levels

open import foundation-core.embeddings
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.sets

open import group-theory.free-groups-with-one-generator
open import group-theory.groups
open import group-theory.homomorphisms-groups
open import group-theory.integer-powers-of-elements-groups
open import group-theory.isomorphisms-groups
open import group-theory.kernels-homomorphisms-groups
open import group-theory.precategory-of-groups
open import group-theory.trivial-subgroups
```

</details>

## Idea

A [group homomorphism](group-theory.homomorphisms-groups.md) `f : x → y` is a
**monomorphism** if whenever we have two group homomorphisms `g h : w → x` such
that `f ∘ g = f ∘ h`, then in fact `g = h`. The way to state this in Homotopy
Type Theory is to say that postcomposition by `f` is an
[embedding](foundation-core.embeddings.md).

## Definition

```agda
module _
  {l1 l2 : Level} (l3 : Level) (G : Group l1)
  (H : Group l2) (f : hom-Group G H)
  where

  is-mono-prop-hom-Group : Prop (l1 ⊔ l2 ⊔ lsuc l3)
  is-mono-prop-hom-Group =
    is-mono-prop-Large-Precategory Group-Large-Precategory l3 G H f

  is-mono-hom-Group : UU (l1 ⊔ l2 ⊔ lsuc l3)
  is-mono-hom-Group = type-Prop is-mono-prop-hom-Group

  is-prop-is-mono-hom-Group : is-prop is-mono-hom-Group
  is-prop-is-mono-hom-Group = is-prop-type-Prop is-mono-prop-hom-Group
```

## Properties

### Isomorphisms are monomorphisms

```agda
module _
  {l1 l2 : Level} (l3 : Level) (G : Group l1)
  (H : Group l2) (f : iso-Group G H)
  where

  is-mono-iso-Group : is-mono-hom-Group l3 G H (hom-iso-Group G H f)
  is-mono-iso-Group =
    is-mono-iso-Large-Precategory Group-Large-Precategory l3 G H f
```

### Monomorphisms are [injective](foundation.injective-maps.md)

```agda
{-
module _
  {l1 l2 l3 : Level} (G : Group l1) (H : Group l2) (f : hom-Group G H)
  (f-mono : is-mono-hom-Group l3 G H f)
  where

  is-mono-is-injective-Group : is-injective (map-hom-Group G H f)
  is-mono-is-injective-Group {x} {y} p =
    inv (integer-power-one-Group G x) ∙ htpy-2 one-ℤ ∙
      integer-power-one-Group G y where
    x-ℤ : hom-Group ℤ-Group G
    x-ℤ = hom-element-Group G x

    y-ℤ : hom-Group ℤ-Group G
    y-ℤ = hom-element-Group G y

    htpy-1 :
      htpy-hom-Group ℤ-Group H (comp-hom-Group ℤ-Group G H f x-ℤ)
      ( comp-hom-Group ℤ-Group G H f y-ℤ)
    htpy-1 =
      inv-htpy (htpy-hom-element-Group H (map-hom-Group G H f x)
      ( comp-hom-Group ℤ-Group G H f x-ℤ) lem-1) ∙h lem-3 ∙h
      htpy-hom-element-Group H (map-hom-Group G H f y)
      ( comp-hom-Group ℤ-Group G H f y-ℤ) lem-2 where
        lem-1 :
          map-hom-Group ℤ-Group H (comp-hom-Group ℤ-Group G H f
          ( hom-element-Group G x)) one-ℤ ＝ pr1 f x
        lem-1 =
          preserves-integer-powers-hom-Group G H f one-ℤ x ∙
          integer-power-one-Group H (pr1 f x)

        lem-2 :
          map-hom-Group ℤ-Group H (comp-hom-Group ℤ-Group G H f
          ( hom-element-Group G y)) one-ℤ ＝ pr1 f y
        lem-2 =
          preserves-integer-powers-hom-Group G H f one-ℤ y ∙
          integer-power-one-Group H (pr1 f y)

        lem-3 :
          map-hom-element-Group H (pr1 f x) ~ map-hom-element-Group H (pr1 f y)
        lem-3 z = ap (integer-power-Group H z) p

    eq-1 :
      (comp-hom-Group ℤ-Group G H f x-ℤ) ＝ (comp-hom-Group ℤ-Group G H f y-ℤ)
    eq-1 = eq-htpy-hom-Group ℤ-Group H htpy-1

    eq-2 : x-ℤ ＝ y-ℤ
    eq-2 =
      map-equiv (inv-equiv-ap-emb
      (( λ g → comp-hom-Group ℤ-Group G H f g) , {!   !})) eq-1

    htpy-2 : htpy-hom-Group ℤ-Group G x-ℤ y-ℤ
    htpy-2 = htpy-eq-hom-Group ℤ-Group G x-ℤ y-ℤ eq-2
-}
```

### `f : G → H` is a monomorphism when it is [injective](foundation-core.injective-maps.md)

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2) (f : hom-Group G H)
  (f-inj : is-injective (map-hom-Group G H f))
  where

  is-injective-is-mono-Group : {l : Level} → is-mono-hom-Group l G H f
  pr1 (pr1 (is-injective-is-mono-Group K g h)) comp =
    eq-htpy-hom-Group K G htpy where
    htpy : htpy-hom-Group K G g h
    htpy x =
      f-inj (htpy-eq-hom-Group K H (comp-hom-Group K G H f g)
      ( comp-hom-Group K G H f h) comp x)
  pr2 (pr1 (is-injective-is-mono-Group K g h)) comp =
    is-set-has-uip (is-set-hom-Group K H) (comp-hom-Group K G H f g)
    ( comp-hom-Group K G H f h)
    (( ap (comp-hom-Large-Precategory Group-Large-Precategory f) ∘
    pr1 (pr1 (is-injective-is-mono-Group K g h))) comp) comp
  pr1 (pr2 (is-injective-is-mono-Group K g h)) comp =
    eq-htpy-hom-Group K G htpy where
    htpy : htpy-hom-Group K G g h
    htpy x =
      f-inj (htpy-eq-hom-Group K H (comp-hom-Group K G H f g)
      ( comp-hom-Group K G H f h) comp x)
  pr2 (pr2 (is-injective-is-mono-Group K g h)) p =
    is-set-has-uip (is-set-hom-Group K G) g h
    (( pr1 (pr2 (is-injective-is-mono-Group K g h)) ∘
    ap (comp-hom-Large-Precategory Group-Large-Precategory f)) p) p
```

### `f : G → H` is a monomorphism iff its [kernel](group-theory.kernels-homomorphisms-groups.md) is [trivial](group-theory.trivial-subgroups.md)

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2) (f : hom-Group G H)
  where

  kernel-is-trivial-is-mono-Group :
    {l : Level} → is-trivial-Subgroup G (subgroup-kernel-hom-Group G H f) →
    is-mono-hom-Group l G H f
  kernel-is-trivial-is-mono-Group f-ker-triv =
    is-injective-is-mono-Group G H f
    ( kernel-is-trivial-is-injective-Group G H f f-ker-triv)
  {-
  is-mono-kernel-is-trivial-Group :
    {l : Level} → is-mono-hom-Group l G H f →
    is-trivial-Subgroup G (subgroup-kernel-hom-Group G H f)
  is-mono-kernel-is-trivial-Group f-mono x x-in-ker =
    is-mono-is-injective-Group G H f f-mono
    ( preserves-unit-hom-Group G H f ∙ x-in-ker)
    -}
```
