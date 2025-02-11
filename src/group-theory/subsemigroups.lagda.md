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
open import foundation.large-binary-relations
open import foundation.powersets
open import foundation.propositions
open import foundation.sets
open import foundation.subtype-identity-principle
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.homomorphisms-semigroups
open import group-theory.semigroups
open import group-theory.subsets-semigroups

open import order-theory.large-posets
open import order-theory.large-preorders
open import order-theory.order-preserving-maps-large-posets
open import order-theory.order-preserving-maps-large-preorders
open import order-theory.posets
open import order-theory.preorders
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
  implicit-Π-Prop
    ( type-Semigroup G)
    ( λ x →
      implicit-Π-Prop
        ( type-Semigroup G)
        ( λ y → hom-Prop (P x) (hom-Prop (P y) (P (mul-Semigroup G x y)))))

is-closed-under-multiplication-subset-Semigroup :
  {l1 l2 : Level} (G : Semigroup l1) (P : subset-Semigroup l2 G) → UU (l1 ⊔ l2)
is-closed-under-multiplication-subset-Semigroup G P =
  type-Prop (is-closed-under-multiplication-prop-subset-Semigroup G P)

Subsemigroup :
  {l1 : Level} (l2 : Level) (G : Semigroup l1) → UU (l1 ⊔ lsuc l2)
Subsemigroup l2 G =
  type-subtype
    ( is-closed-under-multiplication-prop-subset-Semigroup {l2 = l2} G)

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

  has-same-elements-prop-Subsemigroup :
    {l3 : Level} → Subsemigroup l3 G → Prop (l1 ⊔ l2 ⊔ l3)
  has-same-elements-prop-Subsemigroup K =
    has-same-elements-subtype-Prop
      ( subset-Subsemigroup G H)
      ( subset-Subsemigroup G K)

  has-same-elements-Subsemigroup :
    {l3 : Level} → Subsemigroup l3 G → UU (l1 ⊔ l2 ⊔ l3)
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
      ( λ x → id , id)
      ( extensionality-subtype (subset-Subsemigroup G H))

  refl-has-same-elements-Subsemigroup : has-same-elements-Subsemigroup H
  refl-has-same-elements-Subsemigroup =
    refl-has-same-elements-subtype (subset-Subsemigroup G H)

  has-same-elements-eq-Subsemigroup :
    (K : Subsemigroup l2 G) → (H ＝ K) → has-same-elements-Subsemigroup K
  has-same-elements-eq-Subsemigroup K =
    map-equiv (extensionality-Subsemigroup K)

  eq-has-same-elements-Subsemigroup :
    (K : Subsemigroup l2 G) → has-same-elements-Subsemigroup K → (H ＝ K)
  eq-has-same-elements-Subsemigroup K =
    map-inv-equiv (extensionality-Subsemigroup K)
```

### The containment relation of subsemigroups

```agda
leq-prop-Subsemigroup :
  {l1 l2 l3 : Level} (G : Semigroup l1) →
  Subsemigroup l2 G → Subsemigroup l3 G → Prop (l1 ⊔ l2 ⊔ l3)
leq-prop-Subsemigroup G H K =
  leq-prop-subtype
    ( subset-Subsemigroup G H)
    ( subset-Subsemigroup G K)

leq-Subsemigroup :
  {l1 l2 l3 : Level} (G : Semigroup l1) →
  Subsemigroup l2 G → Subsemigroup l3 G → UU (l1 ⊔ l2 ⊔ l3)
leq-Subsemigroup G H K = subset-Subsemigroup G H ⊆ subset-Subsemigroup G K

is-prop-leq-Subsemigroup :
  {l1 l2 l3 : Level} (G : Semigroup l1) →
  (H : Subsemigroup l2 G) (K : Subsemigroup l3 G) →
  is-prop (leq-Subsemigroup G H K)
is-prop-leq-Subsemigroup G H K =
  is-prop-leq-subtype (subset-Subsemigroup G H) (subset-Subsemigroup G K)

refl-leq-Subsemigroup :
  {l1 : Level} (G : Semigroup l1) →
  is-reflexive-Large-Relation (λ l → Subsemigroup l G) (leq-Subsemigroup G)
refl-leq-Subsemigroup G H = refl-leq-subtype (subset-Subsemigroup G H)

transitive-leq-Subsemigroup :
  {l1 : Level} (G : Semigroup l1) →
  is-transitive-Large-Relation (λ l → Subsemigroup l G) (leq-Subsemigroup G)
transitive-leq-Subsemigroup G H K L =
  transitive-leq-subtype
    ( subset-Subsemigroup G H)
    ( subset-Subsemigroup G K)
    ( subset-Subsemigroup G L)

antisymmetric-leq-Subsemigroup :
  {l1 : Level} (G : Semigroup l1) →
  is-antisymmetric-Large-Relation (λ l → Subsemigroup l G) (leq-Subsemigroup G)
antisymmetric-leq-Subsemigroup G H K α β =
  eq-has-same-elements-Subsemigroup G H K (λ x → (α x , β x))

Subsemigroup-Large-Preorder :
  {l1 : Level} (G : Semigroup l1) →
  Large-Preorder (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
type-Large-Preorder (Subsemigroup-Large-Preorder G) l2 = Subsemigroup l2 G
leq-prop-Large-Preorder (Subsemigroup-Large-Preorder G) H K =
  leq-prop-Subsemigroup G H K
refl-leq-Large-Preorder (Subsemigroup-Large-Preorder G) =
  refl-leq-Subsemigroup G
transitive-leq-Large-Preorder (Subsemigroup-Large-Preorder G) =
  transitive-leq-Subsemigroup G

Subsemigroup-Preorder :
  {l1 : Level} (l2 : Level) (G : Semigroup l1) →
  Preorder (l1 ⊔ lsuc l2) (l1 ⊔ l2)
Subsemigroup-Preorder l2 G =
  preorder-Large-Preorder (Subsemigroup-Large-Preorder G) l2

Subsemigroup-Large-Poset :
  {l1 : Level} (G : Semigroup l1) →
  Large-Poset (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
large-preorder-Large-Poset (Subsemigroup-Large-Poset G) =
  Subsemigroup-Large-Preorder G
antisymmetric-leq-Large-Poset (Subsemigroup-Large-Poset G) =
  antisymmetric-leq-Subsemigroup G

Subsemigroup-Poset :
  {l1 : Level} (l2 : Level) (G : Semigroup l1) →
  Poset (l1 ⊔ lsuc l2) (l1 ⊔ l2)
Subsemigroup-Poset l2 G = poset-Large-Poset (Subsemigroup-Large-Poset G) l2

preserves-order-subset-Subsemigroup :
  {l1 l2 l3 : Level}
  (G : Semigroup l1) (H : Subsemigroup l2 G) (K : Subsemigroup l3 G) →
  leq-Subsemigroup G H K → (subset-Subsemigroup G H ⊆ subset-Subsemigroup G K)
preserves-order-subset-Subsemigroup G H K = id

subset-subsemigroup-hom-large-poset-Semigroup :
  {l1 : Level} (G : Semigroup l1) →
  hom-Large-Poset
    ( λ l → l)
    ( Subsemigroup-Large-Poset G)
    ( powerset-Large-Poset (type-Semigroup G))
map-hom-Large-Preorder
  ( subset-subsemigroup-hom-large-poset-Semigroup G) =
  subset-Subsemigroup G
preserves-order-hom-Large-Preorder
  ( subset-subsemigroup-hom-large-poset-Semigroup G) =
  preserves-order-subset-Subsemigroup G
```
