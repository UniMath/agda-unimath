# The binary action on identifications of binary dependent functions

```agda
module foundation.action-on-identifications-binary-dependent-functions where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.doubly-dependent-identifications
open import foundation.universe-levels

open import foundation-core.identity-types
```

</details>

## Idea

Given a binary dependent function `f : (x : A) (y : B) → C x y` and
[identifications](foundation-core.identity-types.md) `p : x ＝ x'` in `A` and
`q : y ＝ y'` in `B`, we obtain a [doubly dependent identification](foundation.doubly-dependent-identifications.md)

```text
  apd-binary f p q : doubly-dependent-identification p q (f x y) (f x' y')
```

we call this the
{{#concept "binary action on identifications of dependent binary functions" Agda=apd-binary}}.

## Definitions

### The binary action on identifications of binary dependent functions

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : A → B → UU l3}
  (f : (x : A) (y : B) → C x y)
  where

  apd-binary :
    {x x' : A} (p : x ＝ x') {y y' : B} (q : y ＝ y') →
    doubly-dependent-identification C p q (f x y) (f x' y')
  apd-binary refl q = apd (f _) q
```

## See also

- [Action of functions on identifications](foundation.action-on-identifications-functions.md)
- [Action of functions on higher identifications](foundation.action-on-higher-identifications-functions.md).
- [Action of dependent functions on identifications](foundation.action-on-identifications-dependent-functions.md).
