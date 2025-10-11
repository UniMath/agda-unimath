# Large groups

```agda
module group-theory.large-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-types
open import foundation.universe-levels
open import group-theory.groups
open import foundation.large-binary-relations
open import foundation.dependent-pair-types
open import foundation.involutions
open import foundation.automorphisms
open import foundation.equivalences
open import foundation.action-on-identifications-functions
open import group-theory.large-monoids
open import foundation.sets
```

</details>

## Idea

A {{#concept "large group" Agda=Large-Group}} is a
[large monoid](group-theory.large-monoids.md) with an inverse operation `i`,
characterized by `i x ∙ x = x ∙ i x = e`, where `e` is the identity element.

## Definition

```agda
record Large-Group (α : Level → Level) (β : Level → Level → Level) : UUω where
  constructor
    make-Large-Group

  field
    large-monoid-Large-Group : Large-Monoid α β

  type-Large-Group : (l : Level) → UU (α l)
  type-Large-Group = type-Large-Monoid large-monoid-Large-Group

  set-Large-Group : (l : Level) → Set (α l)
  set-Large-Group = set-Large-Monoid large-monoid-Large-Group

  mul-Large-Group :
    {l1 l2 : Level} → type-Large-Group l1 → type-Large-Group l2 →
    type-Large-Group (l1 ⊔ l2)
  mul-Large-Group = mul-Large-Monoid large-monoid-Large-Group

  ap-mul-Large-Group :
    {l1 l2 : Level} →
    {x x' : type-Large-Group l1} → x ＝ x' →
    {y y' : type-Large-Group l2} → y ＝ y' →
    mul-Large-Group x y ＝ mul-Large-Group x' y'
  ap-mul-Large-Group = ap-mul-Large-Monoid large-monoid-Large-Group

  associative-mul-Large-Group :
    {l1 l2 l3 : Level} →
    (x : type-Large-Group l1) →
    (y : type-Large-Group l2) →
    (z : type-Large-Group l3) →
    mul-Large-Group (mul-Large-Group x y) z ＝
    mul-Large-Group x (mul-Large-Group y z)
  associative-mul-Large-Group =
    associative-mul-Large-Monoid large-monoid-Large-Group

  unit-Large-Group : type-Large-Group lzero
  unit-Large-Group = unit-Large-Monoid large-monoid-Large-Group

  raise-unit-Large-Group : (l : Level) → type-Large-Group l
  raise-unit-Large-Group = raise-unit-Large-Monoid large-monoid-Large-Group

  raise-Large-Group :
    {l1 : Level} (l2 : Level) → type-Large-Group l1 → type-Large-Group (l1 ⊔ l2)
  raise-Large-Group = raise-Large-Monoid large-monoid-Large-Group

  raise-raise-Large-Group :
    {l1 l2 l3 : Level} → (x : type-Large-Group l1) →
    raise-Large-Group l2 (raise-Large-Group l3 x) ＝
    raise-Large-Group (l2 ⊔ l3) x
  raise-raise-Large-Group = raise-raise-Large-Monoid large-monoid-Large-Group

  raise-left-mul-Large-Group :
    {l1 l2 l3 : Level} →
    (x : type-Large-Group l1) (y : type-Large-Group l2) →
    mul-Large-Group (raise-Large-Group l3 x) y ＝
    raise-Large-Group l3 (mul-Large-Group x y)
  raise-left-mul-Large-Group =
    raise-left-mul-Large-Monoid large-monoid-Large-Group

  raise-right-mul-Large-Group :
    {l1 l2 l3 : Level} →
    (x : type-Large-Group l1) (y : type-Large-Group l2) →
    mul-Large-Group x (raise-Large-Group l3 y) ＝
    raise-Large-Group l3 (mul-Large-Group x y)
  raise-right-mul-Large-Group =
    raise-right-mul-Large-Monoid large-monoid-Large-Group

  left-unit-law-mul-Large-Group :
    {l : Level} (x : type-Large-Group l) →
    mul-Large-Group unit-Large-Group x ＝ x
  left-unit-law-mul-Large-Group =
    left-unit-law-mul-Large-Monoid large-monoid-Large-Group

  right-unit-law-mul-Large-Group :
    {l : Level} (x : type-Large-Group l) →
    mul-Large-Group x unit-Large-Group ＝ x
  right-unit-law-mul-Large-Group =
    right-unit-law-mul-Large-Monoid large-monoid-Large-Group

  sim-prop-Large-Group : Large-Relation-Prop β type-Large-Group
  sim-prop-Large-Group = sim-prop-Large-Monoid large-monoid-Large-Group

  sim-Large-Group : Large-Relation β type-Large-Group
  sim-Large-Group = sim-Large-Monoid large-monoid-Large-Group

  raise-left-unit-law-Large-Group :
    {l1 l2 : Level} (x : type-Large-Group l1) →
    sim-Large-Group (mul-Large-Group (raise-unit-Large-Group l2) x) x
  raise-left-unit-law-Large-Group =
    raise-left-unit-law-Large-Monoid large-monoid-Large-Group

  raise-left-unit-law-Large-Group' :
    {l1 l2 : Level} (x : type-Large-Group l1) →
    mul-Large-Group (raise-unit-Large-Group l2) x ＝ raise-Large-Group l2 x
  raise-left-unit-law-Large-Group' =
    raise-left-unit-law-Large-Monoid' large-monoid-Large-Group

  raise-right-unit-law-Large-Group :
    {l1 l2 : Level} (x : type-Large-Group l1) →
    sim-Large-Group (mul-Large-Group x (raise-unit-Large-Group l2)) x
  raise-right-unit-law-Large-Group =
    raise-right-unit-law-Large-Monoid large-monoid-Large-Group

  raise-right-unit-law-Large-Group' :
    {l1 l2 : Level} (x : type-Large-Group l1) →
    mul-Large-Group x (raise-unit-Large-Group l2) ＝ raise-Large-Group l2 x
  raise-right-unit-law-Large-Group' =
    raise-right-unit-law-Large-Monoid' large-monoid-Large-Group

  refl-sim-Large-Group :
    {l : Level} (x : type-Large-Group l) → sim-Large-Group x x
  refl-sim-Large-Group = refl-sim-Large-Monoid large-monoid-Large-Group

  sim-eq-Large-Group :
    {l : Level} {x y : type-Large-Group l} → x ＝ y → sim-Large-Group x y
  sim-eq-Large-Group = sim-eq-Large-Monoid large-monoid-Large-Group

  eq-sim-Large-Group :
    {l : Level} (x y : type-Large-Group l) → sim-Large-Group x y → x ＝ y
  eq-sim-Large-Group = eq-sim-Large-Monoid large-monoid-Large-Group

  symmetric-sim-Large-Group :
    {l1 l2 : Level} (x : type-Large-Group l1) (y : type-Large-Group l2) →
    sim-Large-Group x y → sim-Large-Group y x
  symmetric-sim-Large-Group =
    symmetric-sim-Large-Monoid large-monoid-Large-Group

  preserves-sim-left-mul-Large-Group :
    {l1 l2 l3 : Level} (y : type-Large-Group l1) →
    (x : type-Large-Group l2) (x' : type-Large-Group l3) →
    sim-Large-Group x x' →
    sim-Large-Group (mul-Large-Group x y) (mul-Large-Group x' y)
  preserves-sim-left-mul-Large-Group =
    preserves-sim-left-mul-Large-Monoid large-monoid-Large-Group

  preserves-sim-right-mul-Large-Group :
    {l1 l2 l3 : Level} (x : type-Large-Group l1) →
    (y : type-Large-Group l2) (y' : type-Large-Group l3) →
    sim-Large-Group y y' →
    sim-Large-Group (mul-Large-Group x y) (mul-Large-Group x y')
  preserves-sim-right-mul-Large-Group =
    preserves-sim-right-mul-Large-Monoid large-monoid-Large-Group


  raise-unit-lzero-Large-Group :
    raise-unit-Large-Group lzero ＝ unit-Large-Group
  raise-unit-lzero-Large-Group =
    raise-unit-lzero-Large-Monoid large-monoid-Large-Group

  field
    inv-Large-Group : {l : Level} → type-Large-Group l → type-Large-Group l

    preserves-sim-inv-Large-Group :
      {l1 l2 : Level} (x : type-Large-Group l1) (y : type-Large-Group l2) →
      sim-Large-Group x y →
      sim-Large-Group (inv-Large-Group x) (inv-Large-Group y)

    left-inverse-law-mul-Large-Group :
      {l : Level} (x : type-Large-Group l) →
      mul-Large-Group (inv-Large-Group x) x ＝ raise-unit-Large-Group l

    right-inverse-law-mul-Large-Group :
      {l : Level} (x : type-Large-Group l) →
      mul-Large-Group x (inv-Large-Group x) ＝ raise-unit-Large-Group l

  abstract
    inv-unit-Large-Group : inv-Large-Group unit-Large-Group ＝ unit-Large-Group
    inv-unit-Large-Group =
      equational-reasoning
        inv-Large-Group unit-Large-Group
        ＝ mul-Large-Group (inv-Large-Group unit-Large-Group) unit-Large-Group
          by inv (right-unit-law-mul-Large-Group _)
        ＝ raise-unit-Large-Group lzero
          by left-inverse-law-mul-Large-Group _
        ＝ unit-Large-Group
          by raise-unit-lzero-Large-Group

open Large-Group public
```

## Properties

### Similarity reasoning on large groups

```agda
module
  similarity-reasoning-Large-Group
    {α : Level → Level} {β : Level → Level → Level} (G : Large-Group α β)
  where

  open similarity-reasoning-Large-Monoid (large-monoid-Large-Group G) public
```

### Uniqueness of right inverses

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Group α β)
  where

  abstract
    unique-right-inv-Large-Group :
      {l1 l2 : Level} (x : type-Large-Group G l1) (y : type-Large-Group G l2) →
      (mul-Large-Group G x y ＝ raise-unit-Large-Group G (l1 ⊔ l2)) →
      sim-Large-Group G y (inv-Large-Group G x)
    unique-right-inv-Large-Group {l1} {l2} x y xy=1 =
      let
        open similarity-reasoning-Large-Group G
        _*_ = mul-Large-Group G
      in
        similarity-reasoning
          y
          ~ raise-unit-Large-Group G l1 * y
            by
              symmetric-sim-Large-Group G _ _
                ( raise-left-unit-law-Large-Group G y)
          ~ (inv-Large-Group G x * x) * y
            by
              sim-eq-Large-Group G
                ( ap-mul-Large-Group G
                  ( inv (left-inverse-law-mul-Large-Group G x))
                  ( refl))
          ~ inv-Large-Group G x * (x * y)
            by
              sim-eq-Large-Group G (associative-mul-Large-Group G _ _ _)
          ~ inv-Large-Group G x * raise-unit-Large-Group G (l1 ⊔ l2)
            by
              sim-eq-Large-Group G (ap-mul-Large-Group G refl xy=1)
          ~ inv-Large-Group G x
            by raise-right-unit-law-Large-Group G _
```

### Uniqueness of left inverses

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Group α β)
  where

  abstract
    unique-left-inv-Large-Group :
      {l1 l2 : Level} (x : type-Large-Group G l1) (y : type-Large-Group G l2) →
      (mul-Large-Group G x y ＝ raise-unit-Large-Group G (l1 ⊔ l2)) →
      sim-Large-Group G x (inv-Large-Group G y)
    unique-left-inv-Large-Group {l1} {l2} x y xy=1 =
      let
        open similarity-reasoning-Large-Group G
        _*_ = mul-Large-Group G
      in
        similarity-reasoning
          x
          ~ x * raise-unit-Large-Group G l2
            by
              symmetric-sim-Large-Group G _ _
                ( raise-right-unit-law-Large-Group G x)
          ~ x * (y * inv-Large-Group G y)
            by
              sim-eq-Large-Group G
                ( ap-mul-Large-Group G
                  ( refl)
                  ( inv (right-inverse-law-mul-Large-Group G y)))
          ~ (x * y) * inv-Large-Group G y
            by
              sim-eq-Large-Group G (inv (associative-mul-Large-Group G _ _ _))
          ~ raise-unit-Large-Group G (l1 ⊔ l2) * inv-Large-Group G y
            by
              sim-eq-Large-Group G (ap-mul-Large-Group G xy=1 refl)
          ~ inv-Large-Group G y
            by raise-left-unit-law-Large-Group G _
```

### Distributivity of inverses over multiplication

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Group α β)
  where

  abstract
    distributive-inv-mul-Large-Group :
      {l1 l2 : Level} (x : type-Large-Group G l1) (y : type-Large-Group G l2) →
      inv-Large-Group G (mul-Large-Group G x y) ＝
      mul-Large-Group G (inv-Large-Group G y) (inv-Large-Group G x)
    distributive-inv-mul-Large-Group {l1} {l2} x y =
      inv
        ( let
            open similarity-reasoning-Large-Group G
            _*_ = mul-Large-Group G
            neg = inv-Large-Group G
          in
            eq-sim-Large-Group G _ _
              ( unique-right-inv-Large-Group G _ _
                ( equational-reasoning
                  (x * y) * (neg y * neg x)
                  ＝ x * (y * (neg y * neg x))
                    by associative-mul-Large-Group G _ _ _
                  ＝ x * ((y * neg y) * neg x)
                    by
                      ap-mul-Large-Group G
                        ( refl)
                        ( inv (associative-mul-Large-Group G _ _ _))
                  ＝ x * (raise-unit-Large-Group G l2 * neg x)
                    by
                      ap-mul-Large-Group G
                        ( refl)
                        ( ap-mul-Large-Group G
                          ( right-inverse-law-mul-Large-Group G y)
                          ( refl))
                  ＝ x * raise-Large-Group G l2 (neg x)
                    by
                      ap-mul-Large-Group G
                        ( refl)
                        ( raise-left-unit-law-Large-Group' G _)
                  ＝ raise-Large-Group G l2 (x * neg x)
                    by raise-right-mul-Large-Group G _ _
                  ＝ raise-Large-Group G l2 (raise-unit-Large-Group G l1)
                    by
                      ap
                        ( raise-Large-Group G l2)
                        ( right-inverse-law-mul-Large-Group G x)
                  ＝ raise-unit-Large-Group G (l1 ⊔ l2)
                    by raise-raise-Large-Group G _)))
```

### Inverting elements of a large group is an involution

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Group α β)
  where

  inv-inv-Large-Group :
    {l : Level} (x : type-Large-Group G l) →
    inv-Large-Group G (inv-Large-Group G x) ＝ x
  inv-inv-Large-Group x =
    inv
      ( eq-sim-Large-Group G _ _
        ( unique-right-inv-Large-Group G _ _
          ( left-inverse-law-mul-Large-Group G x)))

  aut-inv-Large-Group : (l : Level) → Aut (type-Large-Group G l)
  aut-inv-Large-Group l =
    ( inv-Large-Group G ,
      is-equiv-is-involution inv-inv-Large-Group)
```
