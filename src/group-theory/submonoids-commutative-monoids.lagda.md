# Submonoids of commutative monoids

```agda
module group-theory.submonoids-commutative-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.commutative-monoids
open import group-theory.homomorphisms-commutative-monoids
open import group-theory.monoids
open import group-theory.semigroups
open import group-theory.submonoids
open import group-theory.subsets-commutative-monoids
```

</details>

## Idea

A
{{#concept "submonoid" Disambiguation="of a commutative monoid" Agda=Commutative-Submonoid}}
of a [commutative monoid](group-theory.commutative-monoids.md) `M` is a
[subset](group-theory.subsets-commutative-monoids.md) of `M` that contains the
unit of `M` and is closed under multiplication.

## Definitions

### Submonoids of commutative monoids

```agda
is-submonoid-prop-subset-Commutative-Monoid :
  {l1 l2 : Level} (M : Commutative-Monoid l1)
  (P : subset-Commutative-Monoid l2 M) → Prop (l1 ⊔ l2)
is-submonoid-prop-subset-Commutative-Monoid M =
  is-submonoid-prop-subset-Monoid (monoid-Commutative-Monoid M)

is-submonoid-subset-Commutative-Monoid :
  {l1 l2 : Level} (M : Commutative-Monoid l1)
  (P : subset-Commutative-Monoid l2 M) → UU (l1 ⊔ l2)
is-submonoid-subset-Commutative-Monoid M =
  is-submonoid-subset-Monoid (monoid-Commutative-Monoid M)

Commutative-Submonoid :
  {l1 : Level} (l2 : Level) (M : Commutative-Monoid l1) → UU (l1 ⊔ lsuc l2)
Commutative-Submonoid l2 M =
  Submonoid l2 (monoid-Commutative-Monoid M)

module _
  {l1 l2 : Level} (M : Commutative-Monoid l1) (P : Commutative-Submonoid l2 M)
  where

  subset-Commutative-Submonoid : subtype l2 (type-Commutative-Monoid M)
  subset-Commutative-Submonoid =
    subset-Submonoid (monoid-Commutative-Monoid M) P

  is-submonoid-Commutative-Submonoid :
    is-submonoid-subset-Commutative-Monoid M subset-Commutative-Submonoid
  is-submonoid-Commutative-Submonoid =
    is-submonoid-Submonoid (monoid-Commutative-Monoid M) P

  is-in-Commutative-Submonoid : type-Commutative-Monoid M → UU l2
  is-in-Commutative-Submonoid =
    is-in-Submonoid (monoid-Commutative-Monoid M) P

  is-prop-is-in-Commutative-Submonoid :
    (x : type-Commutative-Monoid M) → is-prop (is-in-Commutative-Submonoid x)
  is-prop-is-in-Commutative-Submonoid =
    is-prop-is-in-Submonoid (monoid-Commutative-Monoid M) P

  is-closed-under-eq-Commutative-Submonoid :
    {x y : type-Commutative-Monoid M} →
    is-in-Commutative-Submonoid x → (x ＝ y) → is-in-Commutative-Submonoid y
  is-closed-under-eq-Commutative-Submonoid =
    is-closed-under-eq-Submonoid (monoid-Commutative-Monoid M) P

  is-closed-under-eq-Commutative-Submonoid' :
    {x y : type-Commutative-Monoid M} →
    is-in-Commutative-Submonoid y → (x ＝ y) → is-in-Commutative-Submonoid x
  is-closed-under-eq-Commutative-Submonoid' =
    is-closed-under-eq-Submonoid' (monoid-Commutative-Monoid M) P

  type-Commutative-Submonoid : UU (l1 ⊔ l2)
  type-Commutative-Submonoid =
    type-Submonoid (monoid-Commutative-Monoid M) P

  is-set-type-Commutative-Submonoid : is-set type-Commutative-Submonoid
  is-set-type-Commutative-Submonoid =
    is-set-type-Submonoid (monoid-Commutative-Monoid M) P

  set-Commutative-Submonoid : Set (l1 ⊔ l2)
  set-Commutative-Submonoid = set-Submonoid (monoid-Commutative-Monoid M) P

  inclusion-Commutative-Submonoid :
    type-Commutative-Submonoid → type-Commutative-Monoid M
  inclusion-Commutative-Submonoid =
    inclusion-Submonoid (monoid-Commutative-Monoid M) P

  ap-inclusion-Commutative-Submonoid :
    (x y : type-Commutative-Submonoid) → x ＝ y →
    inclusion-Commutative-Submonoid x ＝ inclusion-Commutative-Submonoid y
  ap-inclusion-Commutative-Submonoid =
    ap-inclusion-Submonoid (monoid-Commutative-Monoid M) P

  is-in-submonoid-inclusion-Commutative-Submonoid :
    (x : type-Commutative-Submonoid) →
    is-in-Commutative-Submonoid (inclusion-Commutative-Submonoid x)
  is-in-submonoid-inclusion-Commutative-Submonoid =
    is-in-submonoid-inclusion-Submonoid (monoid-Commutative-Monoid M) P

  contains-unit-Commutative-Submonoid :
    is-in-Commutative-Submonoid (unit-Commutative-Monoid M)
  contains-unit-Commutative-Submonoid =
    contains-unit-Submonoid (monoid-Commutative-Monoid M) P

  unit-Commutative-Submonoid : type-Commutative-Submonoid
  unit-Commutative-Submonoid =
    unit-Submonoid (monoid-Commutative-Monoid M) P

  is-closed-under-multiplication-Commutative-Submonoid :
    {x y : type-Commutative-Monoid M} →
    is-in-Commutative-Submonoid x → is-in-Commutative-Submonoid y →
    is-in-Commutative-Submonoid (mul-Commutative-Monoid M x y)
  is-closed-under-multiplication-Commutative-Submonoid =
    is-closed-under-multiplication-Submonoid (monoid-Commutative-Monoid M) P

  mul-Commutative-Submonoid :
    (x y : type-Commutative-Submonoid) → type-Commutative-Submonoid
  mul-Commutative-Submonoid = mul-Submonoid (monoid-Commutative-Monoid M) P

  associative-mul-Commutative-Submonoid :
    (x y z : type-Commutative-Submonoid) →
    (mul-Commutative-Submonoid (mul-Commutative-Submonoid x y) z) ＝
    (mul-Commutative-Submonoid x (mul-Commutative-Submonoid y z))
  associative-mul-Commutative-Submonoid =
    associative-mul-Submonoid (monoid-Commutative-Monoid M) P

  semigroup-Commutative-Submonoid : Semigroup (l1 ⊔ l2)
  semigroup-Commutative-Submonoid =
    semigroup-Submonoid (monoid-Commutative-Monoid M) P

  left-unit-law-mul-Commutative-Submonoid :
    (x : type-Commutative-Submonoid) →
    mul-Commutative-Submonoid unit-Commutative-Submonoid x ＝ x
  left-unit-law-mul-Commutative-Submonoid =
    left-unit-law-mul-Submonoid (monoid-Commutative-Monoid M) P

  right-unit-law-mul-Commutative-Submonoid :
    (x : type-Commutative-Submonoid) →
    mul-Commutative-Submonoid x unit-Commutative-Submonoid ＝ x
  right-unit-law-mul-Commutative-Submonoid =
    right-unit-law-mul-Submonoid (monoid-Commutative-Monoid M) P

  commutative-mul-Commutative-Submonoid :
    (x y : type-Commutative-Submonoid) →
    mul-Commutative-Submonoid x y ＝ mul-Commutative-Submonoid y x
  commutative-mul-Commutative-Submonoid x y =
    eq-type-subtype
      ( subset-Commutative-Submonoid)
      ( commutative-mul-Commutative-Monoid M
        ( inclusion-Commutative-Submonoid x)
        ( inclusion-Commutative-Submonoid y))

  monoid-Commutative-Submonoid : Monoid (l1 ⊔ l2)
  monoid-Commutative-Submonoid =
    monoid-Submonoid (monoid-Commutative-Monoid M) P

  commutative-monoid-Commutative-Submonoid : Commutative-Monoid (l1 ⊔ l2)
  pr1 commutative-monoid-Commutative-Submonoid =
    monoid-Commutative-Submonoid
  pr2 commutative-monoid-Commutative-Submonoid =
    commutative-mul-Commutative-Submonoid

  preserves-unit-inclusion-Commutative-Submonoid :
    inclusion-Commutative-Submonoid unit-Commutative-Submonoid ＝
    unit-Commutative-Monoid M
  preserves-unit-inclusion-Commutative-Submonoid =
    preserves-unit-inclusion-Submonoid (monoid-Commutative-Monoid M) P

  preserves-mul-inclusion-Commutative-Submonoid :
    (x y : type-Commutative-Submonoid) →
    inclusion-Commutative-Submonoid (mul-Commutative-Submonoid x y) ＝
    mul-Commutative-Monoid M
      ( inclusion-Commutative-Submonoid x)
      ( inclusion-Commutative-Submonoid y)
  preserves-mul-inclusion-Commutative-Submonoid x y =
    preserves-mul-inclusion-Submonoid (monoid-Commutative-Monoid M) P {x} {y}

  hom-inclusion-Commutative-Submonoid :
    hom-Commutative-Monoid commutative-monoid-Commutative-Submonoid M
  hom-inclusion-Commutative-Submonoid =
    hom-inclusion-Submonoid (monoid-Commutative-Monoid M) P
```

## Properties

### Extensionality of the type of all submonoids

```agda
module _
  {l1 l2 : Level} (M : Commutative-Monoid l1) (N : Commutative-Submonoid l2 M)
  where

  has-same-elements-Commutative-Submonoid :
    {l3 : Level} → Commutative-Submonoid l3 M → UU (l1 ⊔ l2 ⊔ l3)
  has-same-elements-Commutative-Submonoid =
    has-same-elements-Submonoid (monoid-Commutative-Monoid M) N

  extensionality-Commutative-Submonoid :
    (K : Commutative-Submonoid l2 M) →
    (N ＝ K) ≃ has-same-elements-Commutative-Submonoid K
  extensionality-Commutative-Submonoid =
    extensionality-Submonoid (monoid-Commutative-Monoid M) N
```
