# Binary dependent identifications

```agda
module foundation.binary-dependent-identifications where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-transport
open import foundation.universe-levels

open import foundation-core.identity-types
```

</details>

## Idea

Consider a family of types `C x y` indexed by `x : A` and `y : B`, and consider
[identifications](foundation-core.identity-types.md) `p : x ＝ x'` and
`q : y ＝ y'` in `A` and `B`, respectively. A
{{#concept "binary dependent identification" Agda=binary-dependent-identification}}
from `c : C x y` to `c' : C x' y'` over `p` and `q` is a
[dependent identification](foundation.dependent-identifications.md)

```text
  r : dependent-identification (C x') p (tr (λ t → C t y) p c) c'.
```

## Definitions

### Binary dependent identifications

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : A → B → UU l3)
  where

  binary-dependent-identification :
    {x x' : A} (p : x ＝ x') {y y' : B} (q : y ＝ y') →
    C x y → C x' y' → UU l3
  binary-dependent-identification p q c c' = binary-tr C p q c ＝ c'
```
