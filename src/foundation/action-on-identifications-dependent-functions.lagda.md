# The action on identifications of dependent functions

```agda
module foundation.action-on-identifications-dependent-functions where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import foundation-core.identity-types
open import foundation-core.transport
```

</details>

## Idea

Given a dependent function `f : (x : A) → B x` and an identification
`p : x ＝ y` in `A`, we cannot directly compare the values `f x` and `f y`,
since `f x` is an element of type `B x` while `f y` is an element of type `B y`.
However, we can [transport](foundation-core.transport.md) the value `f x` along
`p` to obtain an element of type `B y` that is comparable to the value `f y`. In
other words, we can consider the type of paths over `p` from `f x` to `f y`. The
**dependent action on identifications** of `f` on `p` is a path over

```text
  apd f p : path-over p (f x) (f y).
```

## Definition

### Functorial action of dependent functions on identity types

```agda
apd :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (f : (x : A) → B x) {x y : A}
  (p : x ＝ y) → tr B p (f x) ＝ f y
apd f refl = refl
```
