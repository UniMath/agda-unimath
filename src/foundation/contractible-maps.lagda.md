# Contractible maps

```agda
module foundation.contractible-maps where

open import foundation-core.contractible-maps public
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.truncated-maps
open import foundation.universe-levels

open import foundation-core.logical-equivalences
open import foundation-core.propositions
open import foundation-core.truncation-levels
```

</details>

## Properties

### Being a contractible map is a property

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-prop-is-contr-map : (f : A → B) → is-prop (is-contr-map f)
  is-prop-is-contr-map f = is-prop-is-trunc-map neg-two-𝕋 f

  is-contr-map-Prop : (A → B) → Prop (l1 ⊔ l2)
  pr1 (is-contr-map-Prop f) = is-contr-map f
  pr2 (is-contr-map-Prop f) = is-prop-is-contr-map f
```

### Being a contractible map is equivalent to being an equivalence

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  equiv-is-equiv-is-contr-map : (f : A → B) → is-contr-map f ≃ is-equiv f
  equiv-is-equiv-is-contr-map f =
    equiv-iff
      ( is-contr-map-Prop f)
      ( is-equiv-Prop f)
      ( is-equiv-is-contr-map)
      ( is-contr-map-is-equiv)

  equiv-is-contr-map-is-equiv : (f : A → B) → is-equiv f ≃ is-contr-map f
  equiv-is-contr-map-is-equiv f =
    equiv-iff
      ( is-equiv-Prop f)
      ( is-contr-map-Prop f)
      ( is-contr-map-is-equiv)
      ( is-equiv-is-contr-map)
```

## See also

- For the notion of biinvertible maps see
  [`foundation.equivalences`](foundation.equivalences.md).
- For the notions of inverses and coherently invertible maps, also known as
  half-adjoint equivalences, see
  [`foundation.coherently-invertible-maps`](foundation.coherently-invertible-maps.md).
- For the notion of path-split maps see
  [`foundation.path-split-maps`](foundation.path-split-maps.md).
