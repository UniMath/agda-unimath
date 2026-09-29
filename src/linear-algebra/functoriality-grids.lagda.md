# Functoriality of the type of grids

```agda
module linear-algebra.functoriality-grids where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.universe-levels

open import linear-algebra.grids

open import lists.functoriality-tuples
```

</details>

## Idea

Any map `f : A → B` induces a map between [grids](linear-algebra.grids.md)
`grid A m n → grid B m n`.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  map-grid : {m n : ℕ} → grid A m n → grid B m n
  map-grid = map-tuple (map-tuple f)
```

### Binary maps

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → B → C)
  where

  binary-map-grid :
    {m n : ℕ} → grid A m n → grid B m n → grid C m n
  binary-map-grid = binary-map-tuple (binary-map-tuple f)
```
