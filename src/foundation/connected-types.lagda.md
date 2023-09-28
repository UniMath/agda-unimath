# Connected types

```agda
module foundation.connected-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.inhabited-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.truncations
open import foundation.universe-levels

open import foundation-core.constant-maps
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
```

</details>

## Idea

A type is said to be **`k`-connected** if its `k`-truncation is contractible.

## Definition

```agda
is-connected-Prop : {l : Level} (k : 𝕋) → UU l → Prop l
is-connected-Prop k A = is-contr-Prop (type-trunc k A)

is-connected : {l : Level} (k : 𝕋) → UU l → UU l
is-connected k A = type-Prop (is-connected-Prop k A)

is-prop-is-connected :
  {l : Level} (k : 𝕋) (A : UU l) → is-prop (is-connected k A)
is-prop-is-connected k A = is-prop-type-Prop (is-connected-Prop k A)
```

## Properties

### A type `A` is `k`-connected if and only if the map `B → (A → B)` is an equivalence for every `k`-truncated type `B`

```agda
is-equiv-diagonal-is-connected :
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} (B : Truncated-Type l2 k) →
  is-connected k A →
  is-equiv (λ (b : type-Truncated-Type B) → const A (type-Truncated-Type B) b)
is-equiv-diagonal-is-connected B H =
  is-equiv-comp
    ( precomp unit-trunc (type-Truncated-Type B))
    ( λ b → const _ _ b)
    ( is-equiv-diagonal-is-contr H (type-Truncated-Type B))
    ( is-truncation-trunc B)
```

### An inhabited type `A` is `k + 1`-connected if and only if its identity types are `k`-connected

```agda
module _
  {l1 : Level} {k : 𝕋} {A : UU l1}
  where

  abstract
    is-inhabited-is-connected :
      is-connected (succ-𝕋 k) A → is-inhabited A
    is-inhabited-is-connected H =
      map-universal-property-trunc
        ( truncated-type-Prop k (is-inhabited-Prop A))
        ( unit-trunc-Prop)
        ( center H)

  abstract
    is-connected-eq-is-connected :
      is-connected (succ-𝕋 k) A → {x y : A} → is-connected k (x ＝ y)
    is-connected-eq-is-connected H {x} {y} =
      is-contr-equiv
        ( unit-trunc x ＝ unit-trunc y)
        ( effectiveness-trunc k x y)
        ( is-prop-is-contr H (unit-trunc x) (unit-trunc y))

  abstract
    is-connected-succ-is-connected-eq :
      is-inhabited A → ((x y : A) → is-connected k (x ＝ y)) →
      is-connected (succ-𝕋 k) A
    is-connected-succ-is-connected-eq H K =
      apply-universal-property-trunc-Prop H
        ( is-connected-Prop (succ-𝕋 k) A)
        ( λ a →
          ( unit-trunc a) ,
          ( function-dependent-universal-property-trunc
            ( Id-Truncated-Type
              ( truncated-type-succ-Truncated-Type
                ( succ-𝕋 k)
                ( trunc (succ-𝕋 k) A))
              ( unit-trunc a))
            ( λ x →
              map-universal-property-trunc
                ( Id-Truncated-Type
                  ( trunc (succ-𝕋 k) A)
                  ( unit-trunc a)
                  ( unit-trunc x))
                ( λ { refl → refl})
                ( center (K a x)))))
```
