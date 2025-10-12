# Large groups

```agda
module group-theory.large-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.automorphisms
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.identity-types
open import foundation.involutions
open import foundation.large-binary-relations
open import foundation.logical-equivalences
open import foundation.propositional-maps
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.groups
open import group-theory.large-monoids
open import group-theory.monoids
open import group-theory.semigroups
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

  mul-Large-Group' :
    {l1 l2 : Level} → type-Large-Group l1 → type-Large-Group l2 →
    type-Large-Group (l1 ⊔ l2)
  mul-Large-Group' x y = mul-Large-Group y x

  ap-mul-Large-Group :
    {l1 l2 : Level} →
    {x x' : type-Large-Group l1} → x ＝ x' →
    {y y' : type-Large-Group l2} → y ＝ y' →
    mul-Large-Group x y ＝ mul-Large-Group x' y'
  ap-mul-Large-Group = ap-mul-Large-Monoid large-monoid-Large-Group

  unit-Large-Group : type-Large-Group lzero
  unit-Large-Group = unit-Large-Monoid large-monoid-Large-Group

  sim-prop-Large-Group : Large-Relation-Prop β type-Large-Group
  sim-prop-Large-Group = sim-prop-Large-Monoid large-monoid-Large-Group

  sim-Large-Group : Large-Relation β type-Large-Group
  sim-Large-Group = sim-Large-Monoid large-monoid-Large-Group

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

  raise-unit-Large-Group : (l : Level) → type-Large-Group l
  raise-unit-Large-Group = raise-unit-Large-Monoid large-monoid-Large-Group

  raise-Large-Group :
    {l1 : Level} (l2 : Level) → type-Large-Group l1 → type-Large-Group (l1 ⊔ l2)
  raise-Large-Group = raise-Large-Monoid large-monoid-Large-Group

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

open Large-Group public
```

## Properties

### Monoid laws

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Group α β)
  where

  associative-mul-Large-Group :
    {l1 l2 l3 : Level} →
    (x : type-Large-Group G l1) →
    (y : type-Large-Group G l2) →
    (z : type-Large-Group G l3) →
    mul-Large-Group G (mul-Large-Group G x y) z ＝
    mul-Large-Group G x (mul-Large-Group G y z)
  associative-mul-Large-Group =
    associative-mul-Large-Monoid (large-monoid-Large-Group G)

  left-unit-law-mul-Large-Group :
    {l : Level} (x : type-Large-Group G l) →
    mul-Large-Group G (unit-Large-Group G) x ＝ x
  left-unit-law-mul-Large-Group =
    left-unit-law-mul-Large-Monoid (large-monoid-Large-Group G)

  right-unit-law-mul-Large-Group :
    {l : Level} (x : type-Large-Group G l) →
    mul-Large-Group G x (unit-Large-Group G) ＝ x
  right-unit-law-mul-Large-Group =
    right-unit-law-mul-Large-Monoid (large-monoid-Large-Group G)
```

### Laws of raising universe levels

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Group α β)
  where

  sim-raise-Large-Group :
    {l1 : Level} (l2 : Level) (x : type-Large-Group G l1) →
    sim-Large-Group G x (raise-Large-Group G l2 x)
  sim-raise-Large-Group = sim-raise-Large-Monoid (large-monoid-Large-Group G)

  sim-raise-Large-Group' :
    {l1 : Level} (l2 : Level) (x : type-Large-Group G l1) →
    sim-Large-Group G (raise-Large-Group G l2 x) x
  sim-raise-Large-Group' = sim-raise-Large-Monoid' (large-monoid-Large-Group G)

  raise-raise-Large-Group :
    {l1 l2 l3 : Level} → (x : type-Large-Group G l1) →
    raise-Large-Group G l2 (raise-Large-Group G l3 x) ＝
    raise-Large-Group G (l2 ⊔ l3) x
  raise-raise-Large-Group =
    raise-raise-Large-Monoid (large-monoid-Large-Group G)

  raise-left-mul-Large-Group :
    {l1 l2 l3 : Level} →
    (x : type-Large-Group G l1) (y : type-Large-Group G l2) →
    mul-Large-Group G (raise-Large-Group G l3 x) y ＝
    raise-Large-Group G l3 (mul-Large-Group G x y)
  raise-left-mul-Large-Group =
    raise-left-mul-Large-Monoid (large-monoid-Large-Group G)

  raise-right-mul-Large-Group :
    {l1 l2 l3 : Level} →
    (x : type-Large-Group G l1) (y : type-Large-Group G l2) →
    mul-Large-Group G x (raise-Large-Group G l3 y) ＝
    raise-Large-Group G l3 (mul-Large-Group G x y)
  raise-right-mul-Large-Group =
    raise-right-mul-Large-Monoid (large-monoid-Large-Group G)

  raise-left-unit-law-Large-Group :
    {l1 l2 : Level} (x : type-Large-Group G l1) →
    mul-Large-Group G (raise-unit-Large-Group G l2) x ＝
    raise-Large-Group G l2 x
  raise-left-unit-law-Large-Group =
    raise-left-unit-law-Large-Monoid (large-monoid-Large-Group G)

  raise-right-unit-law-Large-Group :
    {l1 l2 : Level} (x : type-Large-Group G l1) →
    mul-Large-Group G x (raise-unit-Large-Group G l2) ＝
    raise-Large-Group G l2 x
  raise-right-unit-law-Large-Group =
    raise-right-unit-law-Large-Monoid (large-monoid-Large-Group G)

  raise-unit-lzero-Large-Group :
    raise-unit-Large-Group G lzero ＝ unit-Large-Group G
  raise-unit-lzero-Large-Group =
    raise-unit-lzero-Large-Monoid (large-monoid-Large-Group G)
```

### Similarity reasoning on large groups

```agda
module
  similarity-reasoning-Large-Group
    {α : Level → Level} {β : Level → Level → Level} (G : Large-Group α β)
  where

  open similarity-reasoning-Large-Monoid (large-monoid-Large-Group G) public
```

### The inverse of the identity is the identity

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Group α β)
  where

  abstract
    inv-unit-Large-Group :
      inv-Large-Group G (unit-Large-Group G) ＝ unit-Large-Group G
    inv-unit-Large-Group =
      equational-reasoning
        inv-Large-Group G (unit-Large-Group G)
        ＝
          mul-Large-Group G
            ( inv-Large-Group G (unit-Large-Group G))
            ( unit-Large-Group G)
          by inv (right-unit-law-mul-Large-Group G _)
        ＝ raise-unit-Large-Group G lzero
          by left-inverse-law-mul-Large-Group G _
        ＝ unit-Large-Group G
          by raise-unit-lzero-Large-Group G
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
          ~ raise-Large-Group G l1 y
            by sim-raise-Large-Group G l1 y
          ~ raise-unit-Large-Group G l1 * y
            by sim-eq-Large-Group G (inv (raise-left-unit-law-Large-Group G _))
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
            by sim-eq-Large-Group G (ap-mul-Large-Group G refl xy=1)
          ~ raise-Large-Group G (l1 ⊔ l2) (inv-Large-Group G x)
            by sim-eq-Large-Group G (raise-right-unit-law-Large-Group G _)
          ~ inv-Large-Group G x
            by sim-raise-Large-Group' G _ _
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
          ~ raise-Large-Group G l2 x
            by sim-raise-Large-Group G l2 x
          ~ x * raise-unit-Large-Group G l2
            by sim-eq-Large-Group G (inv (raise-right-unit-law-Large-Group G x))
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
          ~ raise-Large-Group G (l1 ⊔ l2) (inv-Large-Group G y)
            by sim-eq-Large-Group G (raise-left-unit-law-Large-Group G _)
          ~ inv-Large-Group G y
            by sim-raise-Large-Group' G _ _
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
                        ( raise-left-unit-law-Large-Group G _)
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

### The raise operation characterizes the similarity relation

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Group α β)
  where

  sim-iff-eq-raise-Large-Group :
    {l1 l2 : Level} →
    (x : type-Large-Group G l1) (y : type-Large-Group G l2) →
    ( sim-Large-Group G x y) ↔
    ( raise-Large-Group G l2 x ＝ raise-Large-Group G l1 y)
  sim-iff-eq-raise-Large-Group =
    sim-iff-eq-raise-Large-Monoid (large-monoid-Large-Group G)

  sim-eq-raise-Large-Group :
    {l1 l2 : Level} →
    (x : type-Large-Group G l1) (y : type-Large-Group G l2) →
    (raise-Large-Group G l2 x ＝ raise-Large-Group G l1 y) →
    sim-Large-Group G x y
  sim-eq-raise-Large-Group x y =
    backward-implication (sim-iff-eq-raise-Large-Group x y)

  eq-raise-sim-Large-Group :
    {l1 l2 : Level} →
    (x : type-Large-Group G l1) (y : type-Large-Group G l2) →
    sim-Large-Group G x y →
    raise-Large-Group G l2 x ＝ raise-Large-Group G l1 y
  eq-raise-sim-Large-Group x y =
    forward-implication (sim-iff-eq-raise-Large-Group x y)
```

### Small groups from large groups

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Group α β)
  where

  semigroup-Large-Group : (l : Level) → Semigroup (α l)
  semigroup-Large-Group =
    semigroup-Large-Monoid (large-monoid-Large-Group G)

  monoid-Large-Group : (l : Level) → Monoid (α l)
  monoid-Large-Group =
    monoid-Large-Monoid (large-monoid-Large-Group G)

  group-Large-Group : (l : Level) → Group (α l)
  group-Large-Group l =
    ( semigroup-Large-Group l ,
      ( raise-unit-Large-Group G l ,
        left-unit-law-mul-Monoid (monoid-Large-Group l) ,
        right-unit-law-mul-Monoid (monoid-Large-Group l)) ,
      inv-Large-Group G ,
      left-inverse-law-mul-Large-Group G ,
      right-inverse-law-mul-Large-Group G)
```

### Cancellations in a large group

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Group α β)
  where

  open similarity-reasoning-Large-Group G

  private
    _*_ = mul-Large-Group G
    neg = inv-Large-Group G

  abstract
    cancel-left-div-mul-Large-Group :
      {l1 l2 : Level} (x : type-Large-Group G l1) (y : type-Large-Group G l2) →
      mul-Large-Group G
        ( inv-Large-Group G x)
        ( mul-Large-Group G x y) ＝
      raise-Large-Group G l1 y
    cancel-left-div-mul-Large-Group {l1} {l2} x y =
      equational-reasoning
        neg x * (x * y)
        ＝ (neg x * x) * y
          by inv (associative-mul-Large-Group G _ _ _)
        ＝ raise-unit-Large-Group G l1 * y
          by ap-mul-Large-Group G (left-inverse-law-mul-Large-Group G x) refl
        ＝ raise-Large-Group G l1 y
          by raise-left-unit-law-Large-Group G y

    sim-cancel-left-div-mul-Large-Group :
      {l1 l2 : Level} (x : type-Large-Group G l1) (y : type-Large-Group G l2) →
      sim-Large-Group G
        ( mul-Large-Group G (inv-Large-Group G x) (mul-Large-Group G x y))
        ( y)
    sim-cancel-left-div-mul-Large-Group {l1} x y =
      similarity-reasoning
        neg x * (x * y)
        ~ raise-Large-Group G l1 y
          by sim-eq-Large-Group G (cancel-left-div-mul-Large-Group x y)
        ~ y
          by sim-raise-Large-Group' G l1 y

    cancel-left-mul-div-Large-Group :
      {l1 l2 : Level} (x : type-Large-Group G l1) (y : type-Large-Group G l2) →
      mul-Large-Group G
        ( x)
        ( mul-Large-Group G (inv-Large-Group G x) y) ＝
      raise-Large-Group G l1 y
    cancel-left-mul-div-Large-Group {l1} x y =
      equational-reasoning
        x * (neg x * y)
        ＝ neg (neg x) * (neg x * y)
          by ap-mul-Large-Group G (inv (inv-inv-Large-Group G x)) refl
        ＝ raise-Large-Group G l1 y
          by cancel-left-div-mul-Large-Group (neg x) y

    sim-cancel-left-mul-div-Large-Group :
      {l1 l2 : Level} (x : type-Large-Group G l1) (y : type-Large-Group G l2) →
      sim-Large-Group G
        ( mul-Large-Group G x (mul-Large-Group G (inv-Large-Group G x) y))
        ( y)
    sim-cancel-left-mul-div-Large-Group x y =
      tr
        ( λ z → sim-Large-Group G (z * (neg x * y)) y)
        ( inv-inv-Large-Group G x)
        ( sim-cancel-left-div-mul-Large-Group (neg x) y)

    cancel-right-mul-div-Large-Group :
      {l1 l2 : Level} (x : type-Large-Group G l1) (y : type-Large-Group G l2) →
      mul-Large-Group G (mul-Large-Group G y x) (inv-Large-Group G x) ＝
      raise-Large-Group G l1 y
    cancel-right-mul-div-Large-Group {l1} x y =
      equational-reasoning
        (y * x) * neg x
        ＝ y * (x * neg x)
          by associative-mul-Large-Group G _ _ _
        ＝ y * raise-unit-Large-Group G l1
          by ap-mul-Large-Group G refl (right-inverse-law-mul-Large-Group G x)
        ＝ raise-Large-Group G l1 y
          by raise-right-unit-law-Large-Group G y

    sim-cancel-right-mul-div-Large-Group :
      {l1 l2 : Level} (x : type-Large-Group G l1) (y : type-Large-Group G l2) →
      sim-Large-Group G
        ( mul-Large-Group G (mul-Large-Group G y x) (inv-Large-Group G x))
        ( y)
    sim-cancel-right-mul-div-Large-Group {l1} x y =
      similarity-reasoning
        mul-Large-Group G (mul-Large-Group G y x) (inv-Large-Group G x)
        ~ raise-Large-Group G l1 y
          by sim-eq-Large-Group G (cancel-right-mul-div-Large-Group x y)
        ~ y
          by sim-raise-Large-Group' G l1 y

    cancel-right-div-mul-Large-Group :
      {l1 l2 : Level} (x : type-Large-Group G l1) (y : type-Large-Group G l2) →
      mul-Large-Group G (mul-Large-Group G y (inv-Large-Group G x)) x ＝
      raise-Large-Group G l1 y
    cancel-right-div-mul-Large-Group {l1} x y =
      equational-reasoning
        (y * neg x) * x
        ＝ (y * neg x) * neg (neg x)
          by ap-mul-Large-Group G refl (inv (inv-inv-Large-Group G x))
        ＝ raise-Large-Group G l1 y
          by cancel-right-mul-div-Large-Group (neg x) y

    sim-cancel-right-div-mul-Large-Group :
      {l1 l2 : Level} (x : type-Large-Group G l1) (y : type-Large-Group G l2) →
      sim-Large-Group G
        ( mul-Large-Group G (mul-Large-Group G y (inv-Large-Group G x)) x)
        ( y)
    sim-cancel-right-div-mul-Large-Group x y =
      tr
        ( λ z → sim-Large-Group G ((y * neg x) * z) y)
        ( inv-inv-Large-Group G x)
        ( sim-cancel-right-mul-div-Large-Group (neg x) y)
```

### Left multiplication by an element of a large group is an embedding

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Group α β)
  {l1 : Level} (l2 : Level) (x : type-Large-Group G l1)
  where

  abstract
    is-prop-map-left-mul-Large-Group :
      is-prop-map (mul-Large-Group G {l2 = l2} x)
    is-prop-map-left-mul-Large-Group y =
      let
        open similarity-reasoning-Large-Group G
        _*_ = mul-Large-Group G
        neg = inv-Large-Group G
      in
        is-prop-all-elements-equal
          ( λ (z , xz=y) (z' , xz'=y) →
            eq-type-subtype
              ( λ zz →
                Id-Prop
                  ( set-Large-Group G (l1 ⊔ l2))
                  ( mul-Large-Group G x zz)
                  ( y))
              ( eq-sim-Large-Group G _ _
                ( similarity-reasoning
                  z
                  ~ neg x * (x * z)
                    by
                      symmetric-sim-Large-Group G _ _
                        ( sim-cancel-left-div-mul-Large-Group G x z)
                  ~ neg x * (x * z')
                    by
                      sim-eq-Large-Group G
                        ( ap-mul-Large-Group G
                          ( refl)
                          ( xz=y ∙ inv xz'=y))
                  ~ z'
                    by sim-cancel-left-div-mul-Large-Group G x z')))

    is-emb-left-mul-Large-Group : is-emb (mul-Large-Group G {l2 = l2} x)
    is-emb-left-mul-Large-Group =
      is-emb-is-prop-map is-prop-map-left-mul-Large-Group

  emb-left-mul-Large-Group :
    type-Large-Group G l2 ↪ type-Large-Group G (l1 ⊔ l2)
  emb-left-mul-Large-Group =
    ( mul-Large-Group G x , is-emb-left-mul-Large-Group)
```

### Right multiplication by an element of a large group is an embedding

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Group α β)
  {l1 : Level} (l2 : Level) (x : type-Large-Group G l1)
  where

  abstract
    is-prop-map-right-mul-Large-Group :
      is-prop-map (mul-Large-Group' G {l2 = l2} x)
    is-prop-map-right-mul-Large-Group y =
      let
        open similarity-reasoning-Large-Group G
        _*_ = mul-Large-Group G
        neg = inv-Large-Group G
      in
        is-prop-all-elements-equal
          ( λ (z , zx=y) (z' , z'x=y) →
            eq-type-subtype
              ( λ zz →
                Id-Prop
                  ( set-Large-Group G (l1 ⊔ l2))
                  ( mul-Large-Group G zz x)
                  ( y))
              ( eq-sim-Large-Group G _ _
                ( similarity-reasoning
                  z
                  ~ (z * x) * neg x
                    by
                      symmetric-sim-Large-Group G _ _
                        ( sim-cancel-right-mul-div-Large-Group G x z)
                  ~ (z' * x) * neg x
                    by
                      sim-eq-Large-Group G
                        ( ap-mul-Large-Group G
                          ( zx=y ∙ inv z'x=y)
                          ( refl))
                  ~ z'
                    by sim-cancel-right-mul-div-Large-Group G x z')))

    is-emb-right-mul-Large-Group : is-emb (mul-Large-Group' G {l2 = l2} x)
    is-emb-right-mul-Large-Group =
      is-emb-is-prop-map is-prop-map-right-mul-Large-Group

  emb-right-mul-Large-Group :
    type-Large-Group G l2 ↪ type-Large-Group G (l1 ⊔ l2)
  emb-right-mul-Large-Group =
    ( mul-Large-Group' G x , is-emb-right-mul-Large-Group)
```
