# Division in large groups

```agda
module group-theory.division-large-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-types
open import foundation.similarity-preserving-binary-maps-cumulative-large-sets
open import foundation.universe-levels

open import group-theory.large-groups
```

</details>

## Idea

## Definition

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Group α β)
  (let _*G_ = mul-Large-Group G)
  (let inv-G = inv-Large-Group G)
  where

  left-div-Large-Group :
    {l1 l2 : Level} → type-Large-Group G l1 → type-Large-Group G l2 →
    type-Large-Group G (l1 ⊔ l2)
  left-div-Large-Group x y = inv-G y *G x

  right-div-Large-Group :
    {l1 l2 : Level} → type-Large-Group G l1 → type-Large-Group G l2 →
    type-Large-Group G (l1 ⊔ l2)
  right-div-Large-Group x y = x *G inv-G y
```

## Properties

### The division operations preserve similarity

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Group α β)
  (let _*G_ = mul-Large-Group G)
  (let inv-G = inv-Large-Group G)
  where

  abstract
    preserves-sim-left-div-Large-Group :
      preserves-sim-binary-operator-Cumulative-Large-Set
        ( cumulative-large-set-Large-Group G)
        ( left-div-Large-Group G)
    preserves-sim-left-div-Large-Group x x' y y' x~x' y~y' =
      preserves-sim-mul-Large-Group G
        ( inv-G y)
        ( inv-G y')
        ( x)
        ( x')
        ( preserves-sim-inv-Large-Group G y y' y~y')
        ( x~x')

    preserves-sim-right-div-Large-Group :
      preserves-sim-binary-operator-Cumulative-Large-Set
        ( cumulative-large-set-Large-Group G)
        ( right-div-Large-Group G)
    preserves-sim-right-div-Large-Group x x' y y' x~x' y~y' =
      preserves-sim-mul-Large-Group G
        ( x)
        ( x')
        ( inv-G y)
        ( inv-G y')
        ( x~x')
        ( preserves-sim-inv-Large-Group G y y' y~y')

  sim-preserving-binary-operator-left-div-Large-Group :
    sim-preserving-binary-operator-Cumulative-Large-Set
      ( cumulative-large-set-Large-Group G)
  sim-preserving-binary-operator-left-div-Large-Group =
    make-sim-preserving-binary-operator-Cumulative-Large-Set
      ( cumulative-large-set-Large-Group G)
      ( left-div-Large-Group G)
      ( preserves-sim-left-div-Large-Group)

  sim-preserving-binary-operator-right-div-Large-Group :
    sim-preserving-binary-operator-Cumulative-Large-Set
      ( cumulative-large-set-Large-Group G)
  sim-preserving-binary-operator-right-div-Large-Group =
    make-sim-preserving-binary-operator-Cumulative-Large-Set
      ( cumulative-large-set-Large-Group G)
      ( right-div-Large-Group G)
      ( preserves-sim-right-div-Large-Group)
```

### The inverse of `x` left (right) divided by `y` is `y` left (right) divided by `x`

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Group α β)
  (let _*G_ = mul-Large-Group G)
  (let inv-G = inv-Large-Group G)
  where

  abstract
    inv-right-div-Large-Group :
      {l1 l2 : Level} (x : type-Large-Group G l1) (y : type-Large-Group G l2) →
      inv-Large-Group G (right-div-Large-Group G x y) ＝
      right-div-Large-Group G y x
    inv-right-div-Large-Group x y =
      equational-reasoning
        inv-G (x *G inv-G y)
        ＝ inv-G (inv-G y) *G inv-G x
          by distributive-inv-mul-Large-Group G x (inv-G y)
        ＝ y *G inv-G x
          by ap-mul-Large-Group G (inv-inv-Large-Group G y) refl

    inv-left-div-Large-Group :
      {l1 l2 : Level} (x : type-Large-Group G l1) (y : type-Large-Group G l2) →
      inv-Large-Group G (left-div-Large-Group G x y) ＝
      left-div-Large-Group G y x
    inv-left-div-Large-Group x y =
      equational-reasoning
        inv-G (inv-G y *G x)
        ＝ inv-G x *G inv-G (inv-G y)
          by distributive-inv-mul-Large-Group G (inv-G y) x
        ＝ inv-G x *G y
          by ap-mul-Large-Group G refl (inv-inv-Large-Group G y)
```

### Reassociating division

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Group α β)
  {l1 l2 l3 : Level}
  (x : type-Large-Group G l1)
  (y : type-Large-Group G l2)
  (z : type-Large-Group G l3)
  (let _*G_ = mul-Large-Group G)
  (let inv-G = inv-Large-Group G)
  where

  abstract
    associate-right-div-Large-Group :
      right-div-Large-Group G (right-div-Large-Group G x y) z ＝
      right-div-Large-Group G x (mul-Large-Group G z y)
    associate-right-div-Large-Group =
      equational-reasoning
        (x *G inv-G y) *G inv-G z
        ＝ x *G (inv-G y *G inv-G z)
          by associative-mul-Large-Group G x (inv-G y) (inv-G z)
        ＝ x *G inv-G (z *G y)
          by
            ap-mul-Large-Group G
              ( refl)
              ( inv (distributive-inv-mul-Large-Group G z y))

    associate-left-div-Large-Group :
      left-div-Large-Group G (left-div-Large-Group G x y) z ＝
      left-div-Large-Group G x (mul-Large-Group G y z)
    associate-left-div-Large-Group =
      equational-reasoning
        inv-G z *G (inv-G y *G x)
        ＝ (inv-G z *G inv-G y) *G x
          by inv (associative-mul-Large-Group G (inv-G z) (inv-G y) x)
        ＝ inv-G (y *G z) *G x
          by
            ap-mul-Large-Group G
              ( inv (distributive-inv-mul-Large-Group G y z))
              ( refl)
```

### Unit laws of division

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Group α β)
  where

  abstract
    is-unit-law-right-div-Large-Group :
      {l1 l2 : Level} (x : type-Large-Group G l1) (y : type-Large-Group G l2) →
      is-unit-Large-Group G y →
      sim-Large-Group G (right-div-Large-Group G x y) x
    is-unit-law-right-div-Large-Group x y y~1 =
      sim-right-is-unit-law-mul-Large-Group G
        ( x)
        ( inv-Large-Group G y)
        ( inv-is-unit-Large-Group G y y~1)

    unit-law-right-div-Large-Group :
      {l : Level} (x : type-Large-Group G l) →
      right-div-Large-Group G x (unit-Large-Group G) ＝ x
    unit-law-right-div-Large-Group x =
      eq-sim-Large-Group G _ x
        ( is-unit-law-right-div-Large-Group x _ (is-unit-unit-Large-Group G))

    is-unit-law-left-div-Large-Group :
      {l1 l2 : Level} (x : type-Large-Group G l1) (y : type-Large-Group G l2) →
      is-unit-Large-Group G y →
      sim-Large-Group G (left-div-Large-Group G x y) x
    is-unit-law-left-div-Large-Group x y y~1 =
      sim-left-is-unit-law-mul-Large-Group G
        ( inv-Large-Group G y)
        ( x)
        ( inv-is-unit-Large-Group G y y~1)

    unit-law-left-div-Large-Group :
      {l : Level} (x : type-Large-Group G l) →
      left-div-Large-Group G x (unit-Large-Group G) ＝ x
    unit-law-left-div-Large-Group x =
      eq-sim-Large-Group G _ x
        ( is-unit-law-left-div-Large-Group x _ (is-unit-unit-Large-Group G))
```
