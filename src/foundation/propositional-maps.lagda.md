# Propositional maps

```agda
module foundation.propositional-maps where

open import foundation-core.propositional-maps public
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.function-types
open import foundation.logical-equivalences
open import foundation.truncated-maps
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.homotopies
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

### Propositional maps are closed under homotopies

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f g : A → B} (H : f ~ g)
  where

  is-prop-map-htpy : is-prop-map g → is-prop-map f
  is-prop-map-htpy = is-trunc-map-htpy neg-one-𝕋 H
```

### Propositional maps are closed under composition

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (g : B → X) (h : A → B)
  where

  is-prop-map-comp : is-prop-map g → is-prop-map h → is-prop-map (g ∘ h)
  is-prop-map-comp = is-trunc-map-comp neg-one-𝕋 g h

comp-prop-map :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  {X : UU l3} (g : prop-map B X) (h : prop-map A B) →
  prop-map A X
pr1 (comp-prop-map g h) = pr1 g ∘ pr1 h
pr2 (comp-prop-map g h) =
  is-prop-map-comp (pr1 g) (pr1 h) (pr2 g) (pr2 h)
```

### In a commuting triangle `f ~ g ∘ h`, if `g` and `h` are propositional maps, then `f` is a propositional map

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h))
  where

  is-prop-map-left-map-triangle :
    is-prop-map g → is-prop-map h → is-prop-map f
  is-prop-map-left-map-triangle =
    is-trunc-map-left-map-triangle neg-one-𝕋 f g h H
```

### In a commuting triangle `f ~ g ∘ h`, if `f` and `g` are propositional maps, then `h` is a propositional map

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h))
  where

  is-prop-map-top-map-triangle :
    is-prop-map g → is-prop-map f → is-prop-map h
  is-prop-map-top-map-triangle =
    is-trunc-map-top-map-triangle neg-one-𝕋 f g h H
```

### If a composite `g ∘ h` and its left factor `g` are propositional maps, then its right factor `h` is a propositional map

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (g : B → X) (h : A → B)
  where

  is-prop-map-right-factor :
    is-prop-map g → is-prop-map (g ∘ h) → is-prop-map h
  is-prop-map-right-factor =
    is-trunc-map-right-factor neg-one-𝕋 g h
```

### A `-1`-truncated map is `k+1`-truncated

```agda
abstract
  is-trunc-map-is-prop-map :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} {f : A → B} →
    is-prop-map f → is-trunc-map (succ-𝕋 k) f
  is-trunc-map-is-prop-map neg-two-𝕋 H = H
  is-trunc-map-is-prop-map (succ-𝕋 k) H =
    is-trunc-map-succ-is-trunc-map (succ-𝕋 k) (is-trunc-map-is-prop-map k H)
```
