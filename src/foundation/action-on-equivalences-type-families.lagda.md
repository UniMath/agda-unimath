# Action on equivalences of type families

```agda
module foundation.action-on-equivalences-type-families where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-maps
open import foundation.dependent-pair-types
open import foundation.equivalence-induction
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.sets
open import foundation.subuniverses
open import foundation.transport
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.injective-maps
open import foundation-core.propositions
open import foundation-core.subtypes
```

</details>

## Ideas

Given a [subuniverse](foundation.subuniverses.md) `P`, any family of types `B`
indexed by types of `P` has an **action on equivalences**

```text
  (A ≃ B) → P A ≃ P B
```

obtained by [equivalence induction](foundation.equivalence-induction.md). The
acion on equivalences of a type family `B` on a subuniverse `P` of `𝒰` is such
that `B id-equiv ＝ id-equiv`, and fits in a
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

## Definitions

### The action on equivalences of a family of types over a subuniverse

```agda
module _
  { l1 l2 l3 : Level}
  ( P : subuniverse l1 l2) (B : type-subuniverse P → UU l3)
  where

  unique-action-on-equivalences-family-of-types-subuniverse :
    (X : type-subuniverse P) →
    is-contr (fib (ev-id-equiv-subuniverse P X {λ Y e → B X ≃ B Y}) id-equiv)
  unique-action-on-equivalences-family-of-types-subuniverse X =
    is-contr-map-ev-id-equiv-subuniverse P X (λ Y e → B X ≃ B Y) id-equiv

  action-on-equivalences-family-of-types-subuniverse :
    (X Y : type-subuniverse P) → pr1 X ≃ pr1 Y → B X ≃ B Y
  action-on-equivalences-family-of-types-subuniverse X =
    pr1 (center (unique-action-on-equivalences-family-of-types-subuniverse X))

  compute-id-equiv-action-on-equivalences-family-of-types-subuniverse :
    (X : type-subuniverse P) →
    action-on-equivalences-family-of-types-subuniverse X X id-equiv ＝ id-equiv
  compute-id-equiv-action-on-equivalences-family-of-types-subuniverse X =
    pr2 (center (unique-action-on-equivalences-family-of-types-subuniverse X))
```

### The action on equivalences of a family of types over a universe

```agda
module _
  {l1 l2 : Level} (B : UU l1 → UU l2)
  where

  unique-action-on-equivalences-family-of-types-universe :
    {X : UU l1} →
    is-contr (fib (ev-id-equiv (λ Y e → B X ≃ B Y)) id-equiv)
  unique-action-on-equivalences-family-of-types-universe =
    is-contr-map-ev-id-equiv (λ Y e → B _ ≃ B Y) id-equiv

  action-on-equivalences-family-of-types-universe :
    {X Y : UU l1} → (X ≃ Y) → B X ≃ B Y
  action-on-equivalences-family-of-types-universe {X} {Y} =
    pr1 (center (unique-action-on-equivalences-family-of-types-universe {X})) Y

  compute-id-equiv-action-on-equivalences-family-of-types-universe :
    {X : UU l1} →
    action-on-equivalences-family-of-types-universe {X} {X} id-equiv ＝ id-equiv
  compute-id-equiv-action-on-equivalences-family-of-types-universe {X} =
    pr2 (center (unique-action-on-equivalences-family-of-types-universe {X}))
```

## Properties

### The action on equivalences of a family of types over a subuniverse fits in a commuting square with `equiv-eq`

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

commutes for any two types `X Y : type-subuniverse P` and any family of types
`B` over the subuniverse `P`.

```agda
coherence-square-action-on-equivalences-family-of-types-subuniverse :
  {l1 l2 l3 : Level} (P : subuniverse l1 l2) (B : type-subuniverse P → UU l3) →
  (X Y : type-subuniverse P) →
  coherence-square-maps
    ( ap B {X} {Y})
    ( equiv-eq-subuniverse P X Y)
    ( equiv-eq)
    ( action-on-equivalences-family-of-types-subuniverse P B X Y)
coherence-square-action-on-equivalences-family-of-types-subuniverse
  P B X .X refl =
  compute-id-equiv-action-on-equivalences-family-of-types-subuniverse P B X
```

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
coherence-square-action-on-equivalences-family-of-types-universe :
  {l1 l2 : Level} (B : UU l1 → UU l2) (X Y : UU l1) →
  coherence-square-maps
    ( ap B {X} {Y})
    ( equiv-eq)
    ( equiv-eq)
    ( action-on-equivalences-family-of-types-universe B)
coherence-square-action-on-equivalences-family-of-types-universe B X .X refl =
  compute-id-equiv-action-on-equivalences-family-of-types-universe B
```
