# Subsemigroups

```agda
module group-theory.subsemigroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functions
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtype-identity-principle
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.semigroups
```

</details>

## Idea

A subsemigroup of a semigroup `G` is a subtype of `G` closed under multiplication.

## Definitions

### Subsets of semigroups

```agda
subset-Semigroup :
  {l1 : Level} (l2 : Level) (G : Semigroup l1) → UU (l1 ⊔ lsuc l2)
subset-Semigroup l2 G = subtype l2 (type-Semigroup G)

module _
  {l1 l2 : Level} (G : Semigroup l1) (P : subset-Semigroup l2 G)
  where

  is-in-subset-Semigroup : type-Semigroup G → UU l2
  is-in-subset-Semigroup = is-in-subtype P

  is-prop-is-in-subset-Semigroup :
    (x : type-Semigroup G) → is-prop (is-in-subset-Semigroup x)
  is-prop-is-in-subset-Semigroup = is-prop-is-in-subtype P

  type-subset-Semigroup : UU (l1 ⊔ l2)
  type-subset-Semigroup = type-subtype P

  is-set-type-subset-Semigroup : is-set type-subset-Semigroup
  is-set-type-subset-Semigroup =
    is-set-type-subtype P (is-set-type-Semigroup G)

  set-subset-Semigroup : Set (l1 ⊔ l2)
  set-subset-Semigroup = set-subset (set-Semigroup G) P

  inclusion-subset-Semigroup : type-subset-Semigroup → type-Semigroup G
  inclusion-subset-Semigroup = inclusion-subtype P

  ap-inclusion-subset-Semigroup :
    (x y : type-subset-Semigroup) →
    x ＝ y → (inclusion-subset-Semigroup x ＝ inclusion-subset-Semigroup y)
  ap-inclusion-subset-Semigroup = ap-inclusion-subtype P

  is-in-subset-inclusion-subset-Semigroup :
    (x : type-subset-Semigroup) →
    is-in-subset-Semigroup (inclusion-subset-Semigroup x)
  is-in-subset-inclusion-subset-Semigroup =
    is-in-subtype-inclusion-subtype P
```

### Subsemigroups

```agda
is-subsemigroup-subset-Semigroup-Prop :
  {l1 l2 : Level} (G : Semigroup l1) (P : subset-Semigroup l2 G) →
  Prop (l1 ⊔ l2)
is-subsemigroup-subset-Semigroup-Prop G P =
  Π-Prop
    ( type-Semigroup G)
    ( λ x →
      Π-Prop
        ( type-Semigroup G)
        ( λ y → hom-Prop (P x) (hom-Prop (P y) (P (mul-Semigroup G x y)))))

is-subsemigroup-subset-Semigroup :
  {l1 l2 : Level} (G : Semigroup l1) (P : subset-Semigroup l2 G) → UU (l1 ⊔ l2)
is-subsemigroup-subset-Semigroup G P =
  type-Prop (is-subsemigroup-subset-Semigroup-Prop G P)

Subsemigroup :
  {l1 : Level} (l2 : Level) (G : Semigroup l1) → UU (l1 ⊔ lsuc l2)
Subsemigroup l2 G =
  type-subtype (is-subsemigroup-subset-Semigroup-Prop {l2 = l2} G)

module _
  {l1 l2 : Level} (G : Semigroup l1) (P : Subsemigroup l2 G)
  where

  subset-Subsemigroup : subtype l2 (type-Semigroup G)
  subset-Subsemigroup =
    inclusion-subtype (is-subsemigroup-subset-Semigroup-Prop G) P

  is-subsemigroup-Subsemigroup :
    is-subsemigroup-subset-Semigroup G subset-Subsemigroup
  is-subsemigroup-Subsemigroup = pr2 P

  is-in-Subsemigroup : type-Semigroup G → UU l2
  is-in-Subsemigroup = is-in-subtype subset-Subsemigroup

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

  is-closed-under-mul-Subsemigroup :
    {x y : type-Semigroup G} →
    is-in-Subsemigroup x → is-in-Subsemigroup y →
    is-in-Subsemigroup (mul-Semigroup G x y)
  is-closed-under-mul-Subsemigroup {x} {y} = pr2 P x y

  mul-Subsemigroup :
    (x y : type-Subsemigroup) → type-Subsemigroup
  pr1 (mul-Subsemigroup x y) =
    mul-Semigroup G
      ( inclusion-Subsemigroup x)
      ( inclusion-Subsemigroup y)
  pr2 (mul-Subsemigroup x y) =
    is-closed-under-mul-Subsemigroup
      ( is-in-subsemigroup-inclusion-Subsemigroup x)
      ( is-in-subsemigroup-inclusion-Subsemigroup y)

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
      ( is-subsemigroup-subset-Semigroup-Prop G)
      ( is-subsemigroup-Subsemigroup G H)
      ( λ x → pair id id)
      ( extensionality-subtype (subset-Subsemigroup G H))
```
