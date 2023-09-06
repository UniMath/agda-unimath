# The circle

```agda
module synthetic-homotopy-theory.circle where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-types
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.mere-equality
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.transport
open import foundation.universe-levels

open import structured-types.pointed-types

open import synthetic-homotopy-theory.free-loops
open import synthetic-homotopy-theory.universal-property-circle
```

</details>

## Postulates

```agda
postulate 𝕊¹ : UU lzero

postulate base-𝕊¹ : 𝕊¹

postulate loop-𝕊¹ : Id base-𝕊¹ base-𝕊¹

free-loop-𝕊¹ : free-loop 𝕊¹
pr1 free-loop-𝕊¹ = base-𝕊¹
pr2 free-loop-𝕊¹ = loop-𝕊¹

𝕊¹-Pointed-Type : Pointed-Type lzero
pr1 𝕊¹-Pointed-Type = 𝕊¹
pr2 𝕊¹-Pointed-Type = base-𝕊¹

postulate ind-𝕊¹ : {l : Level} → induction-principle-circle l free-loop-𝕊¹
```

## Properties

### The dependent universal property of the circle

```agda
dependent-universal-property-𝕊¹ :
  {l : Level} → dependent-universal-property-circle l free-loop-𝕊¹
dependent-universal-property-𝕊¹ =
  dependent-universal-property-induction-principle-circle free-loop-𝕊¹ ind-𝕊¹

uniqueness-dependent-universal-property-𝕊¹ :
  {l : Level} {P : 𝕊¹ → UU l} (k : free-dependent-loop free-loop-𝕊¹ P) →
  is-contr
    ( Σ ( (x : 𝕊¹) → P x)
        ( λ h →
          Eq-free-dependent-loop free-loop-𝕊¹ P
            ( ev-free-loop-Π free-loop-𝕊¹ P h) k))
uniqueness-dependent-universal-property-𝕊¹ {l} {P} =
  uniqueness-dependent-universal-property-circle
    free-loop-𝕊¹
    dependent-universal-property-𝕊¹

module _
  {l : Level} (P : 𝕊¹ → UU l) (p0 : P base-𝕊¹) (α : Id (tr P loop-𝕊¹ p0) p0)
  where

  Π-𝕊¹ : UU l
  Π-𝕊¹ =
    Σ ( (x : 𝕊¹) → P x)
      ( λ h →
        Eq-free-dependent-loop free-loop-𝕊¹ P
          ( ev-free-loop-Π free-loop-𝕊¹ P h) (pair p0 α))

  apply-dependent-universal-property-𝕊¹ : Π-𝕊¹
  apply-dependent-universal-property-𝕊¹ =
    center (uniqueness-dependent-universal-property-𝕊¹ (pair p0 α))

  function-apply-dependent-universal-property-𝕊¹ : (x : 𝕊¹) → P x
  function-apply-dependent-universal-property-𝕊¹ =
    pr1 apply-dependent-universal-property-𝕊¹

  base-dependent-universal-property-𝕊¹ :
    Id (function-apply-dependent-universal-property-𝕊¹ base-𝕊¹) p0
  base-dependent-universal-property-𝕊¹ =
    pr1 (pr2 apply-dependent-universal-property-𝕊¹)

  loop-dependent-universal-property-𝕊¹ :
    Id
      ( apd function-apply-dependent-universal-property-𝕊¹ loop-𝕊¹ ∙
        base-dependent-universal-property-𝕊¹)
      ( ap (tr P loop-𝕊¹) base-dependent-universal-property-𝕊¹ ∙ α)
  loop-dependent-universal-property-𝕊¹ =
    pr2 (pr2 apply-dependent-universal-property-𝕊¹)
```

### The universal property of the circle

```agda
universal-property-𝕊¹ :
  {l : Level} → universal-property-circle l free-loop-𝕊¹
universal-property-𝕊¹ =
  universal-property-dependent-universal-property-circle
    free-loop-𝕊¹
    dependent-universal-property-𝕊¹

uniqueness-universal-property-𝕊¹ :
  {l : Level} {X : UU l} (α : free-loop X) →
  is-contr
    ( Σ ( 𝕊¹ → X)
        ( λ h → Eq-free-loop (ev-free-loop free-loop-𝕊¹ X h) α))
uniqueness-universal-property-𝕊¹ {l} {X} =
  uniqueness-universal-property-circle free-loop-𝕊¹ universal-property-𝕊¹ X

module _
  {l : Level} {X : UU l} (x : X) (α : Id x x)
  where

  Map-𝕊¹ : UU l
  Map-𝕊¹ =
    Σ ( 𝕊¹ → X)
      ( λ h → Eq-free-loop (ev-free-loop free-loop-𝕊¹ X h) (pair x α))

  apply-universal-property-𝕊¹ : Map-𝕊¹
  apply-universal-property-𝕊¹ =
    center (uniqueness-universal-property-𝕊¹ (pair x α))

  map-apply-universal-property-𝕊¹ : 𝕊¹ → X
  map-apply-universal-property-𝕊¹ =
    pr1 apply-universal-property-𝕊¹

  base-universal-property-𝕊¹ :
    Id (map-apply-universal-property-𝕊¹ base-𝕊¹) x
  base-universal-property-𝕊¹ =
    pr1 (pr2 apply-universal-property-𝕊¹)

  loop-universal-property-𝕊¹ :
    Id
      ( ap map-apply-universal-property-𝕊¹ loop-𝕊¹ ∙
        base-universal-property-𝕊¹)
      ( base-universal-property-𝕊¹ ∙ α)
  loop-universal-property-𝕊¹ =
    pr2 (pr2 apply-universal-property-𝕊¹)
```

### The circle is 0-connected

```agda
mere-eq-𝕊¹ : (x y : 𝕊¹) → mere-eq x y
mere-eq-𝕊¹ =
  function-apply-dependent-universal-property-𝕊¹
    ( λ x → (y : 𝕊¹) → mere-eq x y)
    ( function-apply-dependent-universal-property-𝕊¹
      ( mere-eq base-𝕊¹)
      ( refl-mere-eq base-𝕊¹)
      ( eq-is-prop is-prop-type-trunc-Prop))
    ( eq-is-prop (is-prop-Π (λ y → is-prop-type-trunc-Prop)))

is-0-connected-𝕊¹ : is-0-connected 𝕊¹
is-0-connected-𝕊¹ = is-0-connected-mere-eq base-𝕊¹ (mere-eq-𝕊¹ base-𝕊¹)
```
