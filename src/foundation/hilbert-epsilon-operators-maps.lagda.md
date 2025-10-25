# Hilbert ε-operators on maps

```agda
module foundation.hilbert-epsilon-operators-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.hilberts-epsilon-operators
open import foundation.images
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.injective-maps
open import foundation-core.sections
```

</details>

## Idea

A
{{#concept "Hilbert ε-operator" Disambiguation="on a map" Agda=ε-operator-map}}
on a map $f : A → B$ is a family of
[Hilbert ε-operators](foundation.hilberts-epsilon-operators.md) on its
[fibers](foundation-core.fibers-of-maps.md). I.e., for every `y : B` there is an
operator

```text
  ε_y : ║ fiber f y ║₋₁ → fiber f y.
```

Some authors also refer to this as _split support_ {{#cite KECA17}}. Contrary to
Hilbert, we do not assume that such an operator exists for every map.

## Definitions

### The structure of a Hilbert ε-operator on a map

```agda
ε-operator-map :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
ε-operator-map {B = B} f = (y : B) → ε-operator-Hilbert (fiber f y)
```

## Properties

### ε-operators on maps are sections of the image-unit

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  map-section-map-unit-im-ε-operator-map : ε-operator-map f → im f → A
  map-section-map-unit-im-ε-operator-map ε (y , p) = pr1 (ε y p)

  is-section-map-section-map-unit-im-ε-operator-map :
    (ε : ε-operator-map f) →
    is-section (map-unit-im f) (map-section-map-unit-im-ε-operator-map ε)
  is-section-map-section-map-unit-im-ε-operator-map ε (y , p) =
    eq-Eq-im f _ _ (pr2 (ε y p))

  section-map-unit-im-ε-operator-map :
    ε-operator-map f → section (map-unit-im f)
  section-map-unit-im-ε-operator-map ε =
    ( map-section-map-unit-im-ε-operator-map ε ,
      is-section-map-section-map-unit-im-ε-operator-map ε)
```

### Injective maps with ε-operators are embeddings

**Proof.** Given a map `f : A → B` equipped with an ε-operator, then we have a
section of the image projection map `A ↠ im f` given by the Hilbert ε-operator.
Now, by injectivity of `f` we the image projection map must be an equivalence.
Hence, `f` is a composite of embeddings and so must be an embedding as well.

```text
    im f
    ↟ ⋮   \
    │ ⋮ ~   \
    │ ↓       ∨
     A ──────→ B
          f
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  is-emb-is-injective-ε-operator-map :
    ε-operator-map f → is-injective f → is-emb f
  is-emb-is-injective-ε-operator-map ε H =
    is-emb-comp
      ( inclusion-im f)
      ( map-unit-im f)
      ( is-emb-inclusion-im f)
      ( is-emb-is-equiv
        ( is-equiv-is-injective
          ( section-map-unit-im-ε-operator-map ε)
          ( is-injective-right-factor (inclusion-im f) (map-unit-im f) H)))
```
