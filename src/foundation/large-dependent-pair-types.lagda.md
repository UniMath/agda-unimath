# Large dependent pair types

```agda
module foundation.large-dependent-pair-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels
```

</details>

## Idea

When `B` is a family of large types over `A`, then we can form the large type of
pairs `pairω a b` consisting of an element `a : A` and an element `b : B a`.
Such pairs are called dependent pairs, since the type of the second component
depends on the first component.

## Definition

```agda
record Σω (A : UUω) (B : A → UUω) : UUω where
  eta-equality
  constructor pairω
  field
    prω1 : A
    prω2 : B prω1

open Σω public

infixr 3 _,ω_
pattern _,ω_ a b = pairω a b
```

### Families on dependent pair types

```agda
module _
  {l : Level} {A : UUω} {B : A → UUω}
  where

  fam-Σω : ((x : A) → B x → UU l) → Σω A B → UU l
  fam-Σω C (pairω x y) = C x y
```
