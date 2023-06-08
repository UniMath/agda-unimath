# Propositional maps

```agda
module foundation.propositional-maps where

open import foundation-core.propositional-maps public
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.truncated-maps
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.logical-equivalences
open import foundation-core.propositions
open import foundation-core.truncation-levels
```

</details>

## Properties

### Being a propositional map is a property

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-prop-is-prop-map : (f : A → B) → is-prop (is-prop-map f)
  is-prop-is-prop-map f = is-prop-is-trunc-map neg-one-𝕋 f

  is-prop-map-Prop : (A → B) → Prop (l1 ⊔ l2)
  pr1 (is-prop-map-Prop f) = is-prop-map f
  pr2 (is-prop-map-Prop f) = is-prop-is-prop-map f
```

### Being a propositional map is equivalent to being an embedding

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  equiv-is-emb-is-prop-map : (f : A → B) → is-prop-map f ≃ is-emb f
  equiv-is-emb-is-prop-map f =
    equiv-iff
      ( is-prop-map-Prop f)
      ( is-emb-Prop f)
      ( is-emb-is-prop-map)
      ( is-prop-map-is-emb)

  equiv-is-prop-map-is-emb : (f : A → B) → is-emb f ≃ is-prop-map f
  equiv-is-prop-map-is-emb f =
    equiv-iff
      ( is-emb-Prop f)
      ( is-prop-map-Prop f)
      ( is-prop-map-is-emb)
      ( is-emb-is-prop-map)
```
