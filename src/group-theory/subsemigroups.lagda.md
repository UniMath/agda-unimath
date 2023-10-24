# Subsemigroups

```agda
module group-theory.subsemigroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtype-identity-principle
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.homomorphisms-semigroups
open import group-theory.semigroups
open import group-theory.subsets-semigroups
```

</details>

## Idea

A subsemigroup of a semigroup `G` is a subtype of `G` closed under
multiplication.

## Definitions

### Subsemigroups

```agda
is-closed-under-multiplication-prop-subset-Semigroup :
  {l1 l2 : Level} (G : Semigroup l1) (P : subset-Semigroup l2 G) →
  Prop (l1 ⊔ l2)
is-closed-under-multiplication-prop-subset-Semigroup G P =
  Π-Prop'
    ( type-Semigroup G)
    ( λ x →
      Π-Prop'
        ( type-Semigroup G)
        ( λ y → hom-Prop (P x) (hom-Prop (P y) (P (mul-Semigroup G x y)))))

is-closed-under-multiplication-subset-Semigroup :
  {l1 l2 : Level} (G : Semigroup l1) (P : subset-Semigroup l2 G) → UU (l1 ⊔ l2)
is-closed-under-multiplication-subset-Semigroup G P =
  type-Prop (is-closed-under-multiplication-prop-subset-Semigroup G P)

Subsemigroup :
  {l1 : Level} (l2 : Level) (G : Semigroup l1) → UU (l1 ⊔ lsuc l2)
Subsemigroup l2 G =
  type-subtype (is-closed-under-multiplication-prop-subset-Semigroup {l2 = l2} G)

module _
  {l1 l2 : Level} (G : Semigroup l1) (P : Subsemigroup l2 G)
  where

  subset-Subsemigroup : subtype l2 (type-Semigroup G)
  subset-Subsemigroup =
    inclusion-subtype (is-closed-under-multiplication-prop-subset-Semigroup G) P

  is-closed-under-multiplication-Subsemigroup :
    is-closed-under-multiplication-subset-Semigroup G subset-Subsemigroup
  is-closed-under-multiplication-Subsemigroup = pr2 P

  is-in-Subsemigroup : type-Semigroup G → UU l2
  is-in-Subsemigroup = is-in-subtype subset-Subsemigroup

  is-closed-under-eq-Subsemigroup :
    {x y : type-Semigroup G} →
    is-in-Subsemigroup x → x ＝ y → is-in-Subsemigroup y
  is-closed-under-eq-Subsemigroup =
    is-closed-under-eq-subset-Semigroup G subset-Subsemigroup

  is-closed-under-eq-Subsemigroup' :
    {x y : type-Semigroup G} →
    is-in-Subsemigroup y → x ＝ y → is-in-Subsemigroup x
  is-closed-under-eq-Subsemigroup' =
    is-closed-under-eq-subset-Semigroup' G subset-Subsemigroup

  is-prop-is-in-Subsemigroup :
    (x : type-Semigroup G) → is-prop (is-in-Subsemigroup x)
  is-prop-is-in-Subsemigroup =
    is-prop-is-in-subtype subset-Subsemigroup

  type-Subsemigroup : UU (l1 ⊔ l2)
  type-Subsemigroup = type-subtype subset-Subsemigroup

  is-set-type-Subsemigroup : is-set type-Subsemigroup
  is-set-type-Subsemigroup =
    is-set-type-subset-Semigroup G subset-Subsemigroup

  set-Subsemigroup : Set (l1 ⊔ l2)
  set-Subsemigroup =
    set-subset-Semigroup G subset-Subsemigroup

  inclusion-Subsemigroup :
    type-Subsemigroup → type-Semigroup G
  inclusion-Subsemigroup =
    inclusion-subtype subset-Subsemigroup

  ap-inclusion-Subsemigroup :
    (x y : type-Subsemigroup) → x ＝ y →
    inclusion-Subsemigroup x ＝ inclusion-Subsemigroup y
  ap-inclusion-Subsemigroup =
    ap-inclusion-subtype subset-Subsemigroup

  is-in-subsemigroup-inclusion-Subsemigroup :
    (x : type-Subsemigroup) →
    is-in-Subsemigroup (inclusion-Subsemigroup x)
  is-in-subsemigroup-inclusion-Subsemigroup =
    is-in-subtype-inclusion-subtype subset-Subsemigroup

  mul-Subsemigroup :
    (x y : type-Subsemigroup) → type-Subsemigroup
  pr1 (mul-Subsemigroup x y) =
    mul-Semigroup G
      ( inclusion-Subsemigroup x)
      ( inclusion-Subsemigroup y)
  pr2 (mul-Subsemigroup x y) =
    is-closed-under-multiplication-Subsemigroup (pr2 x) (pr2 y)

  associative-mul-Subsemigroup :
    (x y z : type-Subsemigroup) →
    ( mul-Subsemigroup (mul-Subsemigroup x y) z) ＝
    ( mul-Subsemigroup x (mul-Subsemigroup y z))
  associative-mul-Subsemigroup x y z =
    eq-type-subtype
      ( subset-Subsemigroup)
      ( associative-mul-Semigroup G
        ( inclusion-Subsemigroup x)
        ( inclusion-Subsemigroup y)
        ( inclusion-Subsemigroup z))

  semigroup-Subsemigroup : Semigroup (l1 ⊔ l2)
  pr1 semigroup-Subsemigroup = set-Subsemigroup
  pr1 (pr2 semigroup-Subsemigroup) = mul-Subsemigroup
  pr2 (pr2 semigroup-Subsemigroup) = associative-mul-Subsemigroup

  preserves-mul-inclusion-Subsemigroup :
    preserves-mul-Semigroup semigroup-Subsemigroup G inclusion-Subsemigroup
  preserves-mul-inclusion-Subsemigroup = refl

  hom-inclusion-Subsemigroup :
    hom-Semigroup semigroup-Subsemigroup G
  pr1 hom-inclusion-Subsemigroup = inclusion-Subsemigroup
  pr2 hom-inclusion-Subsemigroup {x} {y} =
    preserves-mul-inclusion-Subsemigroup {x} {y}
```

## Properties

### Extensionality of the type of all subsemigroups

```agda
module _
  {l1 l2 : Level} (G : Semigroup l1) (H : Subsemigroup l2 G)
  where

  has-same-elements-Subsemigroup : Subsemigroup l2 G → UU (l1 ⊔ l2)
  has-same-elements-Subsemigroup K =
    has-same-elements-subtype
      ( subset-Subsemigroup G H)
      ( subset-Subsemigroup G K)

  extensionality-Subsemigroup :
    (K : Subsemigroup l2 G) → (H ＝ K) ≃ has-same-elements-Subsemigroup K
  extensionality-Subsemigroup =
    extensionality-type-subtype
      ( is-closed-under-multiplication-prop-subset-Semigroup G)
      ( is-closed-under-multiplication-Subsemigroup G H)
      ( λ x → pair id id)
      ( extensionality-subtype (subset-Subsemigroup G H))
```
