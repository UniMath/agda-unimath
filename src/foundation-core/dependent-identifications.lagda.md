# Dependent identifications

```agda
module foundation-core.dependent-identifications where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import foundation-core.identity-types
open import foundation-core.transport
```

</details>

## Idea

Consider a type family `B` over `A`, an
[identification](foundation-core.identity-types.md) `p : x ＝ y` in `A`, and two
elements `u : B x` and `v : B y`. A **path over** `p` from `u` to `v` is an
identification

```text
  tr B p u ＝ v,
```

where `tr` is the [transport](foundation-core.transport.md) function.

## Definition

```agda
dependent-identification :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) {x x' : A} (p : x ＝ x') →
  B x → B x' → UU l2
dependent-identification B p u v = (tr B p u ＝ v)

refl-dependent-identification :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) {x : A} {y : B x} →
  dependent-identification B refl y y
refl-dependent-identification B = refl
```
