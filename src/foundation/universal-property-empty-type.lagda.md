# The universal property of the empty type

```agda
module foundation.universal-property-empty-type where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.universal-property-equivalences
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.function-types
```

</details>

## Idea

There is a unique map from the empty type into any type. Similarly, for any type
family over an empty type, there is a unique dependent function taking values in
this family.

## Definitions

### The initial map into a type

```agda
initial-map : {l : Level} (A : UU l) → empty → A
initial-map A = ex-falso
```

## Properties

```agda
module _
  {l1 : Level} (A : UU l1)
  where

  dependent-universal-property-empty : (l : Level) → UU (l1 ⊔ lsuc l)
  dependent-universal-property-empty l =
    (P : A → UU l) → is-contr ((x : A) → P x)

  universal-property-empty : (l : Level) → UU (l1 ⊔ lsuc l)
  universal-property-empty l = (X : UU l) → is-contr (A → X)

  universal-property-dependent-universal-property-empty :
    ({l : Level} → dependent-universal-property-empty l) →
    ({l : Level} → universal-property-empty l)
  universal-property-dependent-universal-property-empty dup-empty X =
    dup-empty (λ _ → X)

  is-empty-universal-property-empty :
    ({l : Level} → universal-property-empty l) → is-empty A
  is-empty-universal-property-empty up-empty = center (up-empty empty)

  dependent-universal-property-empty-is-empty :
    {l : Level} (H : is-empty A) → dependent-universal-property-empty l
  pr1 (dependent-universal-property-empty-is-empty {l} H P) x = ex-falso (H x)
  pr2 (dependent-universal-property-empty-is-empty {l} H P) f =
    eq-htpy (λ x → ex-falso (H x))

  universal-property-empty-is-empty :
    {l : Level} (H : is-empty A) → universal-property-empty l
  universal-property-empty-is-empty {l} H =
    universal-property-dependent-universal-property-empty
      ( dependent-universal-property-empty-is-empty H)

abstract
  dependent-universal-property-empty' :
    {l : Level} (P : empty → UU l) → is-contr ((x : empty) → P x)
  pr1 (dependent-universal-property-empty' P) = ind-empty {P = P}
  pr2 (dependent-universal-property-empty' P) f = eq-htpy ind-empty

abstract
  universal-property-empty' :
    {l : Level} (X : UU l) → is-contr (empty → X)
  universal-property-empty' X =
    dependent-universal-property-empty' (λ _ → X)

abstract
  uniqueness-empty :
    {l : Level} (Y : UU l) →
    ({l' : Level} (X : UU l') → is-contr (Y → X)) →
    is-equiv (ind-empty {P = λ _ → Y})
  uniqueness-empty Y H =
    is-equiv-is-equiv-precomp ind-empty
      ( λ X →
        is-equiv-is-contr
          ( λ g → g ∘ ind-empty)
          ( H X)
          ( universal-property-empty' X))

abstract
  universal-property-empty-is-equiv-ind-empty :
    {l : Level} (X : UU l) → is-equiv (ind-empty {P = λ _ → X}) →
    ((l' : Level) (Y : UU l') → is-contr (X → Y))
  universal-property-empty-is-equiv-ind-empty X is-equiv-ind-empty l' Y =
    is-contr-is-equiv
      ( empty → Y)
      ( λ f → f ∘ ind-empty)
      ( is-equiv-precomp-is-equiv ind-empty is-equiv-ind-empty Y)
      ( universal-property-empty' Y)
```
