# Pointed dependent functions

```agda
module structured-types.pointed-dependent-functions where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.identity-types
open import foundation.universe-levels

open import structured-types.pointed-families-of-types
open import structured-types.pointed-types
```

</details>

## Idea

A {{#concept "pointed dependent function" Agda=pointed-Π}} of a
[pointed family](structured-types.pointed-families-of-types.md) `B` over `A` is
a dependent function of the underlying family taking the base point of `A` to
the base point of `B`.

```agda
module _
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Fam l2 A)
  where

  pointed-Π : UU (l1 ⊔ l2)
  pointed-Π =
    fiber
      ( ev-point (point-Pointed-Type A) {fam-Pointed-Fam A B})
      ( point-Pointed-Fam A B)

  Π∗ = pointed-Π
```

**Note**: the subscript asterisk symbol used for the pointed dependent function
type `Π∗`, and pointed type constructions in general, is the
[asterisk operator](https://codepoints.net/U+2217) `∗` (agda-input: `\ast`), not
the [asterisk](https://codepoints.net/U+002A) `*`.

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A}
  where

  function-pointed-Π :
    pointed-Π A B → (x : type-Pointed-Type A) → fam-Pointed-Fam A B x
  function-pointed-Π = pr1

  preserves-point-function-pointed-Π :
    (f : pointed-Π A B) →
    function-pointed-Π f (point-Pointed-Type A) ＝ point-Pointed-Fam A B
  preserves-point-function-pointed-Π = pr2
```
