# Action on equivalences in type families over subuniverses

```agda
module foundation.action-on-equivalences-type-families-over-subuniverses where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalence-induction
open import foundation.subuniverses
open import foundation.universe-levels

open import foundation-core.commuting-squares-of-maps
open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.univalence
```

</details>

## Ideas

Given a [subuniverse](foundation.subuniverses.md) `P`, any family of types `B`
indexed by types of `P` has an
[action on equivalences](foundation.action-on-equivalences-functions.md)
obtained by using the [univalence axiom](foundation.univalence.md).

## Definitions

### The action on equivalences of a family of types over a subuniverse

```agda
module _
  { l1 l2 l3 : Level}
  ( P : subuniverse l1 l2) (B : type-subuniverse P → UU l3)
  where

  abstract
    unique-action-equiv-family-over-subuniverse :
      (X : type-subuniverse P) →
      is-contr
        ( fiber (ev-id-equiv-subuniverse P X {λ Y e → B X ≃ B Y}) id-equiv)
    unique-action-equiv-family-over-subuniverse X =
      is-contr-map-ev-id-equiv-subuniverse P X (λ Y e → B X ≃ B Y) id-equiv

  action-equiv-family-over-subuniverse :
    (X Y : type-subuniverse P) → pr1 X ≃ pr1 Y → B X ≃ B Y
  action-equiv-family-over-subuniverse X Y =
    equiv-eq ∘ ap B ∘ eq-equiv-subuniverse P

  compute-id-equiv-action-equiv-family-over-subuniverse :
    (X : type-subuniverse P) →
    action-equiv-family-over-subuniverse X X id-equiv ＝ id-equiv
  compute-id-equiv-action-equiv-family-over-subuniverse X =
    ap (equiv-eq ∘ ap B) (compute-eq-equiv-id-equiv-subuniverse P)
```

## Properties

### The action on equivalences of a family of types over a subuniverse fits in a commuting square with `equiv-eq`

We claim that the square

```text
                   ap B
        (X ＝ Y) --------> (B X ＝ B Y)
           |                    |
  equiv-eq |                    | equiv-eq
           ∨                    ∨
        (X ≃ Y) ---------> (B X ≃ B Y).
                     B
```

commutes for any two types `X Y : type-subuniverse P` and any family of types
`B` over the subuniverse `P`.

```agda
coherence-square-action-equiv-family-over-subuniverse :
  {l1 l2 l3 : Level} (P : subuniverse l1 l2) (B : type-subuniverse P → UU l3) →
  (X Y : type-subuniverse P) →
  coherence-square-maps
    ( ap B {X} {Y})
    ( equiv-eq-subuniverse P X Y)
    ( equiv-eq)
    ( action-equiv-family-over-subuniverse P B X Y)
coherence-square-action-equiv-family-over-subuniverse
  P B X .X refl =
  compute-id-equiv-action-equiv-family-over-subuniverse P B X
```
