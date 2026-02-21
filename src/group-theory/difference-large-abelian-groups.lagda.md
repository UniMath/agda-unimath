### Subtraction

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Ab α β)
  where

  left-subtraction-Large-Ab :
    {l1 l2 : Level} → type-Large-Ab G l1 → type-Large-Ab G l2 →
    type-Large-Ab G (l1 ⊔ l2)
  left-subtraction-Large-Ab x y = add-Large-Ab G (neg-Large-Ab G y) x

  right-subtraction-Large-Ab :
    {l1 l2 : Level} → type-Large-Ab G l1 → type-Large-Ab G l2 →
    type-Large-Ab G (l1 ⊔ l2)
  right-subtraction-Large-Ab x y = add-Large-Ab G x (neg-Large-Ab G y)

  abstract
    neg-right-subtraction-Large-Ab :
      {l1 l2 : Level} (x : type-Large-Ab G l1) (y : type-Large-Ab G l2) →
      neg-Large-Ab G (right-subtraction-Large-Ab x y) ＝
      right-subtraction-Large-Ab y x
    neg-right-subtraction-Large-Ab =
      inv-right-div-Large-Group (large-group-Large-Ab G)

    neg-left-subtraction-Large-Ab :
      {l1 l2 : Level} (x : type-Large-Ab G l1) (y : type-Large-Ab G l2) →
      neg-Large-Ab G (left-subtraction-Large-Ab x y) ＝
      left-subtraction-Large-Ab y x
    neg-left-subtraction-Large-Ab =
      inv-left-div-Large-Group (large-group-Large-Ab G)

    eq-left-right-subtraction-Large-Ab :
      {l1 l2 : Level} (x : type-Large-Ab G l1) (y : type-Large-Ab G l2) →
      left-subtraction-Large-Ab x y ＝ right-subtraction-Large-Ab x y
    eq-left-right-subtraction-Large-Ab x y =
      commutative-add-Large-Ab G (neg-Large-Ab G y) x
```

### Interchange laws of subtraction

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Ab α β)
  (let _+G_ = add-Large-Ab G)
  (let neg-G = neg-Large-Ab G)
  where

  abstract
    interchange-right-subtraction-add-Large-Ab :
      {l1 l2 l3 l4 : Level}
      (a : type-Large-Ab G l1) (b : type-Large-Ab G l2)
      (c : type-Large-Ab G l3) (d : type-Large-Ab G l4) →
      right-subtraction-Large-Ab G
        ( add-Large-Ab G a b)
        ( add-Large-Ab G c d) ＝
      add-Large-Ab G
        ( right-subtraction-Large-Ab G a c)
        ( right-subtraction-Large-Ab G b d)
    interchange-right-subtraction-add-Large-Ab a b c d =
      equational-reasoning
        (a +G b) +G neg-G (c +G d)
        ＝ (a +G b) +G (neg-G c +G neg-G d)
          by ap-add-Large-Ab G refl (distributive-neg-add-Large-Ab G c d)
        ＝ (a +G neg-G c) +G (b +G neg-G d)
          by interchange-add-add-Large-Ab G a b (neg-G c) (neg-G d)
```

### Reassociating subtraction

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Ab α β)
  (let _+G_ = add-Large-Ab G)
  (let neg-G = neg-Large-Ab G)
  where

  abstract
    associate-right-subtraction-Large-Ab :
      {l1 l2 l3 : Level}
      (x : type-Large-Ab G l1)
      (y : type-Large-Ab G l2)
      (z : type-Large-Ab G l3) →
      right-subtraction-Large-Ab G (right-subtraction-Large-Ab G x y) z ＝
      right-subtraction-Large-Ab G x (add-Large-Ab G y z)
    associate-right-subtraction-Large-Ab x y z =
      ( associate-right-div-Large-Group (large-group-Large-Ab G) x y z) ∙
      ( ap (right-subtraction-Large-Ab G x) (commutative-add-Large-Ab G z y))
```

### `(x - y) + (y - z) = x - z`

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Ab α β)
  (let _+G_ = add-Large-Ab G)
  (let neg-G = neg-Large-Ab G)
  where

  open similarity-reasoning-Large-Ab G

  abstract
    add-right-subtraction-Large-Ab :
      {l1 l2 l3 : Level}
      (x : type-Large-Ab G l1)
      (y : type-Large-Ab G l2)
      (z : type-Large-Ab G l3) →
      sim-Large-Ab G
        ( add-Large-Ab G
          ( right-subtraction-Large-Ab G x y)
          ( right-subtraction-Large-Ab G y z))
        ( right-subtraction-Large-Ab G x z)
    add-right-subtraction-Large-Ab x y z =
      similarity-reasoning
        (x +G neg-G y) +G (y +G neg-G z)
        ~ x +G (neg-G y +G (y +G neg-G z))
          by sim-eq-Large-Ab G (associative-add-Large-Ab G x (neg-G y) _)
        ~ x +G neg-G z
          by
            preserves-sim-left-add-Large-Ab G x _ _
              ( sim-cancel-left-diff-add-Large-Ab G y (neg-G z))
```

### `(x + z) - (y + z) = x - y`

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Ab α β)
  (let _+G_ = add-Large-Ab G)
  (let neg-G = neg-Large-Ab G)
  where

  open similarity-reasoning-Large-Ab G

  abstract
    right-subtraction-add-Large-Ab :
      {l1 l2 l3 : Level}
      (x : type-Large-Ab G l1)
      (y : type-Large-Ab G l2)
      (z : type-Large-Ab G l3) →
      sim-Large-Ab G
        ( right-subtraction-Large-Ab G
          ( add-Large-Ab G x z)
          ( add-Large-Ab G y z))
        ( right-subtraction-Large-Ab G x y)
    right-subtraction-add-Large-Ab x y z =
      similarity-reasoning
        (x +G z) +G neg-G (y +G z)
        ~ (x +G neg-G y) +G (z +G neg-G z)
          by
            sim-eq-Large-Ab G
              ( interchange-right-subtraction-add-Large-Ab G x z y z)
        ~ x +G neg-G y
          by
            sim-right-is-zero-law-add-Large-Ab G _ _
              ( sim-right-inverse-law-add-Large-Ab G z)
```

### `x - (x - y) = y`

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Ab α β)
  (let _+G_ = add-Large-Ab G)
  (let neg-G = neg-Large-Ab G)
  where

  open similarity-reasoning-Large-Ab G

  abstract
    right-subtraction-right-subtraction-Large-Ab :
      {l1 l2 : Level} (x : type-Large-Ab G l1) (y : type-Large-Ab G l2) →
      sim-Large-Ab G
        ( right-subtraction-Large-Ab G x (right-subtraction-Large-Ab G x y))
        ( y)
    right-subtraction-right-subtraction-Large-Ab x y =
      similarity-reasoning
        x +G neg-G (x +G neg-G y)
        ~ x +G (y +G neg-G x)
          by
            sim-eq-Large-Ab G
              ( ap-add-Large-Ab G refl (neg-right-subtraction-Large-Ab G x y))
        ~ y
          by cancel-right-conjugation-Large-Ab G x y
```

### If `x - y = z`, then `x - z = y`

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Ab α β)
  (let _+G_ = add-Large-Ab G)
  (let neg-G = neg-Large-Ab G)
  where

  open similarity-reasoning-Large-Ab G

  abstract
    transpose-sim-right-subtraction-Large-Ab :
      {l1 l2 l3 : Level}
      (x : type-Large-Ab G l1)
      (y : type-Large-Ab G l2)
      (z : type-Large-Ab G l3) →
      sim-Large-Ab G (right-subtraction-Large-Ab G x y) z →
      sim-Large-Ab G (right-subtraction-Large-Ab G x z) y
    transpose-sim-right-subtraction-Large-Ab x y z x-y~z =
      similarity-reasoning
        x +G neg-G z
        ~ x +G neg-G (x +G neg-G y)
          by
            preserves-sim-left-add-Large-Ab G x _ _
              ( preserves-sim-neg-Large-Ab G _ _
                ( symmetric-sim-Large-Ab G _ _ x-y~z))
        ~ y
          by right-subtraction-right-subtraction-Large-Ab G x y
```

### Unit laws of subtraction

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Ab α β)
  where

  abstract
    is-zero-law-right-subtraction-Large-Ab :
      {l1 l2 : Level} (x : type-Large-Ab G l1) (y : type-Large-Ab G l2) →
      is-zero-Large-Ab G y →
      sim-Large-Ab G (right-subtraction-Large-Ab G x y) x
    is-zero-law-right-subtraction-Large-Ab =
      is-unit-law-right-div-Large-Group (large-group-Large-Ab G)

    zero-law-right-subtraction-Large-Ab :
      {l : Level} (x : type-Large-Ab G l) →
      right-subtraction-Large-Ab G x (zero-Large-Ab G) ＝ x
    zero-law-right-subtraction-Large-Ab =
      unit-law-right-div-Large-Group (large-group-Large-Ab G)
```
