# Dependent identifications

```agda
module foundation-core.dependent-identifications where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import foundation-core.identity-types
open import foundation-core.transport-along-identifications
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

where `tr` is the
[transport](foundation-core.transport-along-identifications.md) function.
Dependent identifications also satisfy groupoid laws, which are formulated
appropriately as dependent identifications. The groupoid laws for dependent
identifications are proven in
[`foundation.dependent-identifications`](foundation.dependent-identifications.md).

## Definition

### Dependent identifications

```agda
dependent-identification :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) {x x' : A} (p : x ＝ x') →
  B x → B x' → UU l2
dependent-identification B p u v = (tr B p u ＝ v)

refl-dependent-identification :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) {x : A} {y : B x} →
  dependent-identification B refl y y
refl-dependent-identification B = refl

dependent-identification' :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) {x x' : A} (p : x ＝ x') →
  B x → B x' → UU l2
dependent-identification' B p u v = (u ＝ inv-tr B p v)

refl-dependent-identification' :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) {x : A} {y : B x} →
  dependent-identification' B refl y y
refl-dependent-identification' B = refl
```

### Iterated dependent identifications

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2)
  where

  dependent-identification² :
    {x y : A} {p q : x ＝ y} (α : p ＝ q)
    {x' : B x} {y' : B y}
    (p' : dependent-identification B p x' y')
    (q' : dependent-identification B q x' y') →
    UU l2
  dependent-identification² α {x'} {y'} p' q' =
    dependent-identification (λ t → dependent-identification B t x' y') α p' q'
```
