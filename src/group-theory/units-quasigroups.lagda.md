# Units in quasigroups

```agda
module group-theory.units-quasigroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.contractible-types
open import foundation-core.subtypes

open import group-theory.quasigroups
```

</details>

## Idea

There are notions of {{#concept "left units" Agda=has-left-unit-Quasigroup}} and
{{#concept "right units" Agda=has-right-unit-Quasigroup}} for
[quasigroups](quasigroups.quasigroups.md). It turns out that, when `Q` has both
a left and right unit, they coincide, and therefore having a unit is a
proposition.

## Definitions

### Left units in quasigroups

```agda
module _
  {l : Level} (Q : Quasigroup l)
  where

  is-left-unit-Quasigroup : (e : type-Quasigroup Q) → UU l
  is-left-unit-Quasigroup e =
    ( x : type-Quasigroup Q) → mul-Quasigroup Q e x ＝ x

  is-prop-is-left-unit-Quasigroup :
    ( e : type-Quasigroup Q) → is-prop (is-left-unit-Quasigroup e)
  is-prop-is-left-unit-Quasigroup e =
    is-prop-Π (λ x → is-set-Quasigroup Q (mul-Quasigroup Q e x) x)

  is-left-unit-Quasigroup-Prop : (e : type-Quasigroup Q) → Prop l
  is-left-unit-Quasigroup-Prop e =
    ( is-left-unit-Quasigroup e) , is-prop-is-left-unit-Quasigroup e

  has-left-unit-Quasigroup : UU l
  has-left-unit-Quasigroup =
    Σ (type-Quasigroup Q) (λ e → is-left-unit-Quasigroup e)

  element-has-left-unit-Quasigroup :
    has-left-unit-Quasigroup → type-Quasigroup Q
  element-has-left-unit-Quasigroup e = pr1 e

  is-left-unit-has-left-unit-Quasigroup :
    (e : has-left-unit-Quasigroup) →
    is-left-unit-Quasigroup (element-has-left-unit-Quasigroup e)
  is-left-unit-has-left-unit-Quasigroup e = pr2 e
```

### Right units in quasigroups

```agda
module _
  {l : Level} (Q : Quasigroup l)
  where

  is-right-unit-Quasigroup : (f : type-Quasigroup Q) → UU l
  is-right-unit-Quasigroup f =
    ( x : type-Quasigroup Q) → mul-Quasigroup Q x f ＝ x

  is-prop-is-right-unit-Quasigroup :
    ( f : type-Quasigroup Q) → is-prop (is-right-unit-Quasigroup f)
  is-prop-is-right-unit-Quasigroup f =
    is-prop-Π (λ x → is-set-Quasigroup Q (mul-Quasigroup Q x f) x)

  is-right-unit-Quasigroup-Prop : (f : type-Quasigroup Q) → Prop l
  is-right-unit-Quasigroup-Prop f =
    ( is-right-unit-Quasigroup f) , is-prop-is-right-unit-Quasigroup f

  has-right-unit-Quasigroup : UU l
  has-right-unit-Quasigroup =
    Σ (type-Quasigroup Q) (λ f → is-right-unit-Quasigroup f)

  element-has-right-unit-Quasigroup :
    has-right-unit-Quasigroup → type-Quasigroup Q
  element-has-right-unit-Quasigroup f = pr1 f

  is-right-unit-has-right-unit-Quasigroup :
    (f : has-right-unit-Quasigroup) →
    is-right-unit-Quasigroup (element-has-right-unit-Quasigroup f)
  is-right-unit-has-right-unit-Quasigroup f = pr2 f
```

### Units in quasigroups

Recall that a **unit** is both a left and right unit.

```agda
module _
  {l : Level} (Q : Quasigroup l)
  where

  has-unit-Quasigroup : UU l
  has-unit-Quasigroup =
    Σ (type-Quasigroup Q)
    ( λ x → is-left-unit-Quasigroup Q x × is-right-unit-Quasigroup Q x)

  units-agree-Quasigroup :
    ( e f : type-Quasigroup Q) →
    is-left-unit-Quasigroup Q e → is-right-unit-Quasigroup Q f → e ＝ f
  units-agree-Quasigroup e f is-left-unit-e is-right-unit-f =
    equational-reasoning
    e
    ＝ mul-Quasigroup Q e f
      by inv (is-right-unit-f e)
    ＝ f
      by is-left-unit-e f

  is-prop-has-unit-Quasigroup : is-prop has-unit-Quasigroup
  is-prop-has-unit-Quasigroup =
    is-prop-all-elements-equal
    ( λ e f → eq-type-subtype
      ( λ x → product-Prop (is-left-unit-Quasigroup-Prop Q x)
      ( is-right-unit-Quasigroup-Prop Q x))
      ( units-agree-Quasigroup (pr1 e) (pr1 f) (pr1 (pr2 e)) (pr2 (pr2 f))))
```
