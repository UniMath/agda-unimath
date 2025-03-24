# The action on equivalences of functions out of subuniverses

```agda
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module foundation.action-on-equivalences-functions-out-of-subuniverses
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-higher-identifications-functions funext
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalence-induction funext univalence
open import foundation.subuniverses funext univalence
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.identity-types
```

</details>

## Idea

Consider a [subuniverse](foundation.subuniverses.md) `P` of `𝒰` and a map
`f : P → B` from the subuniverse `P` into some type `B`. Then `f` has an
**action on equivalences**

```text
  (X ≃ Y) → (f X ＝ f Y)
```

which is uniquely determined by the
[identification](foundation-core.identity-types.md)
`action-equiv f id-equiv ＝ refl`. The action on equivalences fits in a
[commuting square](foundation.commuting-squares-of-maps.md) of maps

```text
                     ap f
       (X = Y) ---------------> (f X = f Y)
          |                          |
 equiv-eq |                          | id
          ∨                          ∨
       (X ≃ Y) ---------------> (f X = f Y)
                action-equiv f
```

## Definitions

```agda
module _
  {l1 l2 l3 : Level} (P : subuniverse l1 l2)
  {B : UU l3} (f : type-subuniverse P → B)
  where

  abstract
    unique-action-equiv-function-subuniverse :
      (X : type-subuniverse P) →
      is-contr
        ( Σ ( (Y : type-subuniverse P) → equiv-subuniverse P X Y → f X ＝ f Y)
            ( λ h → h X id-equiv ＝ refl))
    unique-action-equiv-function-subuniverse X =
      is-contr-map-ev-id-equiv-subuniverse P X
        ( λ Y e → f X ＝ f Y)
        ( refl)

  action-equiv-function-subuniverse :
    (X Y : type-subuniverse P) → equiv-subuniverse P X Y → f X ＝ f Y
  action-equiv-function-subuniverse X Y =
    ap f ∘ eq-equiv-subuniverse P

  compute-action-equiv-function-subuniverse-id-equiv :
    (X : type-subuniverse P) →
    action-equiv-function-subuniverse X X id-equiv ＝ refl
  compute-action-equiv-function-subuniverse-id-equiv X =
    ap² f (compute-eq-equiv-id-equiv-subuniverse P)
```
