# Action on equivalences of type families

```agda
module foundation.action-on-equivalences-type-families where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-equivalences-functions
open import foundation.action-on-identifications-functions
open import foundation.equivalence-induction
open import foundation.univalence
open import foundation.universe-levels
open import foundation.whiskering-higher-homotopies-composition

open import foundation-core.commuting-squares-of-maps
open import foundation-core.constant-maps
open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
```

</details>

## Ideas

Any family of types `B : 𝒰 → 𝒱` over a universe `𝒰` has an **action on
equivalences**

```text
  (A ≃ B) → P A ≃ P B
```

obtained by [equivalence induction](foundation.equivalence-induction.md). The
acion on equivalences of a type family `B` on a universe `𝒰` is uniquely
determined by the identification `B id-equiv ＝ id-equiv`, and fits in a
[commuting square](foundation.commuting-squares-of-maps.md)

```text
                   ap B
        (X ＝ Y) --------> (B X ＝ B Y)
           |                    |
  equiv-eq |                    | equiv-eq
           V                    V
        (X ≃ Y) ---------> (B X ≃ B Y).
                     B
```

**Note:** In general -- in particular in our general constructions below -- we
need the [univalence axiom](foundation.univalence.md) to construct the action on
equivalences of a family of types. However, for many specific type families that
are defined in terms of the basic type constructors, we can construct the action
on equivalences directly without invoking the univalence axiom.

## Definitions

### The action on equivalences of a family of types over a universe

```agda
module _
  {l1 l2 : Level} (B : UU l1 → UU l2)
  where

  abstract
    unique-action-equiv-family :
      {X : UU l1} →
      is-contr (fiber (ev-id-equiv (λ Y e → B X ≃ B Y)) id-equiv)
    unique-action-equiv-family =
      is-contr-map-ev-id-equiv (λ Y e → B _ ≃ B Y) id-equiv

  action-equiv-family :
    {X Y : UU l1} → (X ≃ Y) → B X ≃ B Y
  action-equiv-family {X} {Y} =
    equiv-eq ∘ action-equiv-function B

  compute-action-equiv-family-id-equiv :
    {X : UU l1} →
    action-equiv-family {X} {X} id-equiv ＝ id-equiv
  compute-action-equiv-family-id-equiv {X} =
    ap equiv-eq (compute-action-equiv-function-id-equiv B X)

  map-action-equiv-family : {X Y : UU l1} → X ≃ Y → B X → B Y
  map-action-equiv-family = map-equiv ∘ action-equiv-family
```

## Properties

### The action on equivalences of a family of types over a universe fits in a commuting square with `equiv-eq`

We claim that the square

```text
                   ap B
        (X ＝ Y) --------> (B X ＝ B Y)
           |                    |
  equiv-eq |                    | equiv-eq
           V                    V
        (X ≃ Y) ---------> (B X ≃ B Y).
                     B
```

commutes for any two types `X Y : 𝒰` and any type family `B` over `𝒰`.

```agda
coherence-square-action-equiv-family :
  {l1 l2 : Level} (B : UU l1 → UU l2) (X Y : UU l1) →
  coherence-square-maps
    ( ap B {X} {Y})
    ( equiv-eq)
    ( equiv-eq)
    ( action-equiv-family B)
coherence-square-action-equiv-family B X .X refl =
  compute-action-equiv-family-id-equiv B
```

### The identity function acts trivially on equivalences

```agda
compute-action-equiv-family-id :
  {l : Level} {X Y : UU l} (e : X ≃ Y) → (action-equiv-family id e) ＝ e
compute-action-equiv-family-id e =
  ap equiv-eq (ap-id (eq-equiv e)) ∙ is-section-eq-equiv e
```

### The action on equivalences of a constant map is constant

```agda
compute-action-equiv-family-const :
  {l1 l2 : Level} (B : UU l2) {X Y : UU l1}
  (e : X ≃ Y) → (action-equiv-family (const (UU l1) B) e) ＝ id-equiv
compute-action-equiv-family-const B {X} {Y} e =
  ap equiv-eq (compute-action-equiv-function-const B e)
```

### The action on equivalences of a composite function is the composite of the actions

```agda
distributive-action-equiv-function-comp :
  {l1 l2 l3 : Level} {C : UU l3} (g : UU l2 → C) (f : UU l1 → UU l2)
  {X Y : UU l1} →
  action-equiv-function (g ∘ f) {X} {Y} ~
  action-equiv-function g ∘ action-equiv-family f
distributive-action-equiv-function-comp g f e =
  ( ap-comp g f (eq-equiv e)) ∙
  ( left-whisker-comp² g
    ( inv-htpy is-retraction-eq-equiv)
    ( action-equiv-function f e))

distributive-action-equiv-family-comp :
  {l1 l2 l3 : Level} (g : UU l2 → UU l3) (f : UU l1 → UU l2)
  {X Y : UU l1} →
  action-equiv-family (g ∘ f) {X} {Y} ~
  action-equiv-family g ∘ action-equiv-family f
distributive-action-equiv-family-comp g f e =
  ap equiv-eq (distributive-action-equiv-function-comp g f e)
```

### The action on equivalences of any map preserves composition of equivalences

```agda
distributive-action-equiv-family-comp-equiv :
  {l1 l2 : Level} (f : UU l1 → UU l2) {X Y Z : UU l1} →
  (e : X ≃ Y) (e' : Y ≃ Z) →
  action-equiv-family f (e' ∘e e) ＝
  action-equiv-family f e' ∘e action-equiv-family f e
distributive-action-equiv-family-comp-equiv f e e' =
  ( ap equiv-eq (distributive-action-equiv-function-comp-equiv f e e')) ∙
  ( inv
    ( compute-equiv-eq-concat
      ( action-equiv-function f e)
      ( action-equiv-function f e')))
```

### The action on equivalences of any map preserves inverses

```agda
compute-action-equiv-family-inv-equiv :
  {l1 l2 : Level} (f : UU l1 → UU l2) {X Y : UU l1}
  (e : X ≃ Y) →
  action-equiv-family f (inv-equiv e) ＝ inv-equiv (action-equiv-family f e)
compute-action-equiv-family-inv-equiv f e =
  ( ap equiv-eq (compute-action-equiv-function-inv-equiv f e)) ∙
  ( inv (commutativity-inv-equiv-eq (action-equiv-function f e)))
```
