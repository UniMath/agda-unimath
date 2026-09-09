# The action on dependent identifications of functions

```agda
module foundation.action-on-dependent-identifications-functions where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import foundation-core.dependent-identifications
open import foundation-core.identity-types
```

</details>

## Idea

Given a type family `B : A → UU l` and an
[identification](foundation-core.identity-types.md) `p : x ＝ y` in `A`, a
function `f : (x : A) → (u : B x) → C` maps a
[dependent-identification](foundation-core.dependent-identifications.md)
`q : dependent-identification B p u v` to an identification
`adp : (f x u) ＝ (f y v)` in `C`.

## Definition

### The action of families of functions on dependent identifications

```agda
adp :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : UU l3}
  (f : (x : A) → (u : B x) → C) {x y : A} {u : B x} {v : B y}
  (p : x ＝ y) (q : dependent-identification B p u v) → (f x u) ＝ (f y v)
adp f refl refl = refl
```

## See also

- [Action of functions on identifications](foundation.action-on-identifications-functions.md)
- [Action of functions on higher identifications](foundation.action-on-higher-identifications-functions.md).
- [Action of binary functions on identifications](foundation.action-on-identifications-binary-functions.md).
