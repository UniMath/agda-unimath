# Local commutative rings

```agda
module commutative-algebra.local-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import ring-theory.local-rings
open import ring-theory.rings
```

</details>

## Idea

A {{#concept "local commutative ring" Agda=Local-Commutative-Ring}} is a
[commutative ring](commutative-algebra.commutative-rings.md) that is
[local](ring-theory.local-rings.md).

A local commutative ring is one limited version of the classical notion of field
that applies usefully in constructive contexts.

## Definition

```agda
is-local-prop-Commutative-Ring :
  {l : Level} (A : Commutative-Ring l) → Prop l
is-local-prop-Commutative-Ring A = is-local-prop-Ring (ring-Commutative-Ring A)

is-local-Commutative-Ring : {l : Level} → Commutative-Ring l → UU l
is-local-Commutative-Ring A = is-local-Ring (ring-Commutative-Ring A)

is-prop-is-local-Commutative-Ring :
  {l : Level} (A : Commutative-Ring l) → is-prop (is-local-Commutative-Ring A)
is-prop-is-local-Commutative-Ring A =
  is-prop-is-local-Ring (ring-Commutative-Ring A)

Local-Commutative-Ring : (l : Level) → UU (lsuc l)
Local-Commutative-Ring l = Σ (Commutative-Ring l) is-local-Commutative-Ring

module _
  {l : Level} (A : Local-Commutative-Ring l)
  where

  commutative-ring-Local-Commutative-Ring : Commutative-Ring l
  commutative-ring-Local-Commutative-Ring = pr1 A

  ring-Local-Commutative-Ring : Ring l
  ring-Local-Commutative-Ring =
    ring-Commutative-Ring commutative-ring-Local-Commutative-Ring

  set-Local-Commutative-Ring : Set l
  set-Local-Commutative-Ring = set-Ring ring-Local-Commutative-Ring

  type-Local-Commutative-Ring : UU l
  type-Local-Commutative-Ring =
    type-Ring ring-Local-Commutative-Ring

  is-local-commutative-ring-Local-Commutative-Ring :
    is-local-Commutative-Ring commutative-ring-Local-Commutative-Ring
  is-local-commutative-ring-Local-Commutative-Ring = pr2 A

  zero-Local-Commutative-Ring : type-Local-Commutative-Ring
  zero-Local-Commutative-Ring = zero-Ring ring-Local-Commutative-Ring

  is-zero-prop-Local-Commutative-Ring : type-Local-Commutative-Ring → Prop l
  is-zero-prop-Local-Commutative-Ring =
    is-zero-ring-Prop ring-Local-Commutative-Ring

  one-Local-Commutative-Ring : type-Local-Commutative-Ring
  one-Local-Commutative-Ring = one-Ring ring-Local-Commutative-Ring

  add-Local-Commutative-Ring :
    type-Local-Commutative-Ring → type-Local-Commutative-Ring →
    type-Local-Commutative-Ring
  add-Local-Commutative-Ring = add-Ring ring-Local-Commutative-Ring

  mul-Local-Commutative-Ring :
    type-Local-Commutative-Ring → type-Local-Commutative-Ring →
    type-Local-Commutative-Ring
  mul-Local-Commutative-Ring = mul-Ring ring-Local-Commutative-Ring

  neg-Local-Commutative-Ring :
    type-Local-Commutative-Ring → type-Local-Commutative-Ring
  neg-Local-Commutative-Ring = neg-Ring ring-Local-Commutative-Ring
```

## See also

- [Heyting fields](commutative-algebra.heyting-fields.md), a local commutative
  ring with stronger constraints on invertibility
