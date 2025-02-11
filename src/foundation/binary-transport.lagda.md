# Binary transport

```agda
module foundation.binary-transport where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.transport-along-identifications
```

</details>

## Idea

Given a binary relation `B : A → A → UU` and identifications `p : x ＝ x'` and
`q : y ＝ y'` in `A`, the binary transport of `B` is an operation

```text
  binary-tr B p q : B x y → B x' y'
```

## Definition

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : A → B → UU l3)
  {x x' : A} {y y' : B}
  where

  binary-tr : (p : x ＝ x') (q : y ＝ y') → C x y → C x' y'
  binary-tr p q c = tr (C x') q (tr (λ u → C u y) p c)

  is-equiv-binary-tr : (p : x ＝ x') (q : y ＝ y') → is-equiv (binary-tr p q)
  is-equiv-binary-tr refl refl = is-equiv-id

  equiv-binary-tr : (p : x ＝ x') (q : y ＝ y') → C x y ≃ C x' y'
  pr1 (equiv-binary-tr p q) = binary-tr p q
  pr2 (equiv-binary-tr p q) = is-equiv-binary-tr p q

  compute-binary-tr :
    (p : x ＝ x') (q : y ＝ y') (u : C x y) →
    tr (λ a → C a y') p (tr (C x) q u) ＝ binary-tr p q u
  compute-binary-tr refl refl u = refl

  compute-binary-tr' :
    (p : x ＝ x') (q : y ＝ y') (u : C x y) →
    tr (C x') q (tr (λ a → C a y) p u) ＝ binary-tr p q u
  compute-binary-tr' refl refl u = refl
```

## Properties

### Transposing binary path-overs

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : A → B → UU l3)
  where

  transpose-binary-path-over :
    {x1 x2 : A} (p : x1 ＝ x2) {y1 y2 : B} (q : y1 ＝ y2)
    {c1 : C x1 y1} {c2 : C x2 y2} →
    c2 ＝ binary-tr C p q c1 → binary-tr C (inv p) (inv q) c2 ＝ c1
  transpose-binary-path-over refl refl = id

  transpose-binary-path-over' :
    {x1 x2 : A} (p : x1 ＝ x2) {y1 y2 : B} (q : y1 ＝ y2)
    {c1 : C x1 y1} {c2 : C x2 y2} →
    c1 ＝ binary-tr C (inv p) (inv q) c2 → binary-tr C p q c1 ＝ c2
  transpose-binary-path-over' refl refl = id
```

### Binary transport along concatenated paths

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : A → B → UU l3)
  where

  binary-tr-concat :
    {x1 x2 x3 : A} (p : x1 ＝ x2) (p' : x2 ＝ x3)
    {y1 y2 y3 : B} (q : y1 ＝ y2) (q' : y2 ＝ y3) →
    (c : C x1 y1) →
    binary-tr C (p ∙ p') (q ∙ q') c ＝
    binary-tr C p' q' (binary-tr C p q c)
  binary-tr-concat refl refl refl refl c = refl
```

### Binary transport along paths of the form `ap f p` and `ap g q`

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  {E : A → C → UU l5} (F : B → D → UU l6)
  {f : A → B} {g : C → D} (h : (a : A) (c : C) → E a c → F (f a) (g c))
  where

  binary-tr-ap :
    {x x' : A} (p : x ＝ x') {y y' : C} (q : y ＝ y') →
    {u : E x y} {v : E x' y'} (r : binary-tr E p q u ＝ v) →
    binary-tr F (ap f p) (ap g q) (h x y u) ＝ h x' y' v
  binary-tr-ap refl refl refl = refl
```
