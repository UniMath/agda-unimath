# The complement of the image of a map

```agda
module foundation.complements-images where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.fundamental-theorem-of-identity-types
open import foundation.negation
open import foundation.subtype-identity-principle
open import foundation.universe-levels

open import foundation-core.1-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.propositions
open import foundation-core.sets
open import foundation-core.subtypes
open import foundation-core.torsorial-type-families
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
```

</details>

## Idea

The {{#concept "complement" Disambiguation="of the image of a map" Agda=nonim}}
of the [image](foundation.images.md) of a map `f : A → B` is the collection of
elements `y` in `B` such that the fiber of `f` over `y` is
[empty](foundation.empty-types.md).

## Definitions

```agda
module _
  {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X)
  where

  subtype-nonim : subtype (l1 ⊔ l2) X
  subtype-nonim x = neg-type-Prop (fiber f x)

  is-in-nonim : X → UU (l1 ⊔ l2)
  is-in-nonim = is-in-subtype subtype-nonim

  nonim : UU (l1 ⊔ l2)
  nonim = type-subtype subtype-nonim

  inclusion-nonim : nonim → X
  inclusion-nonim = inclusion-subtype subtype-nonim
```

## Properties

### We characterize the identity type of `nonim f`

```agda
module _
  {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X)
  where

  Eq-nonim : nonim f → nonim f → UU l1
  Eq-nonim x y = (pr1 x ＝ pr1 y)

  refl-Eq-nonim : (x : nonim f) → Eq-nonim x x
  refl-Eq-nonim x = refl

  Eq-eq-nonim : (x y : nonim f) → x ＝ y → Eq-nonim x y
  Eq-eq-nonim x .x refl = refl-Eq-nonim x

  abstract
    is-torsorial-Eq-nonim :
      (x : nonim f) → is-torsorial (Eq-nonim x)
    is-torsorial-Eq-nonim (x , p) =
      is-torsorial-Eq-subtype (is-torsorial-Id x) (λ x → is-prop-neg) x refl p

  abstract
    is-equiv-Eq-eq-nonim : (x y : nonim f) → is-equiv (Eq-eq-nonim x y)
    is-equiv-Eq-eq-nonim x =
      fundamental-theorem-id (is-torsorial-Eq-nonim x) (Eq-eq-nonim x)

  equiv-Eq-eq-nonim : (x y : nonim f) → (x ＝ y) ≃ Eq-nonim x y
  equiv-Eq-eq-nonim x y = (Eq-eq-nonim x y , is-equiv-Eq-eq-nonim x y)

  eq-Eq-nonim : (x y : nonim f) → Eq-nonim x y → x ＝ y
  eq-Eq-nonim x y = map-inv-is-equiv (is-equiv-Eq-eq-nonim x y)
```

### The nonimage inclusion is an embedding

```agda
abstract
  is-emb-inclusion-nonim :
    {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
    is-emb (inclusion-nonim f)
  is-emb-inclusion-nonim f = is-emb-inclusion-subtype (neg-type-Prop ∘ fiber f)

emb-nonim :
  {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) → nonim f ↪ X
emb-nonim f = (inclusion-nonim f , is-emb-inclusion-nonim f)
```

### The nonimage inclusion is injective

```agda
abstract
  is-injective-inclusion-nonim :
    {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
    is-injective (inclusion-nonim f)
  is-injective-inclusion-nonim f =
    is-injective-is-emb (is-emb-inclusion-nonim f)
```

### The nonimage of a map into a truncated type is truncated

```agda
abstract
  is-trunc-nonim :
    {l1 l2 : Level} (k : 𝕋) {X : UU l1} {A : UU l2} (f : A → X) →
    is-trunc (succ-𝕋 k) X → is-trunc (succ-𝕋 k) (nonim f)
  is-trunc-nonim k f = is-trunc-emb k (emb-nonim f)

nonim-Truncated-Type :
  {l1 l2 : Level} (k : 𝕋) (X : Truncated-Type l1 (succ-𝕋 k)) {A : UU l2}
  (f : A → type-Truncated-Type X) → Truncated-Type (l1 ⊔ l2) (succ-𝕋 k)
nonim-Truncated-Type k X f =
  ( nonim f , is-trunc-nonim k f (is-trunc-type-Truncated-Type X))
```

### The nonimage of a map into a proposition is a proposition

```agda
abstract
  is-prop-nonim :
    {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
    is-prop X → is-prop (nonim f)
  is-prop-nonim = is-trunc-nonim neg-two-𝕋

nonim-Prop :
    {l1 l2 : Level} (X : Prop l1) {A : UU l2}
    (f : A → type-Prop X) → Prop (l1 ⊔ l2)
nonim-Prop X f = nonim-Truncated-Type neg-two-𝕋 X f
```

### The nonimage of a map into a set is a set

```agda
abstract
  is-set-nonim :
    {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
    is-set X → is-set (nonim f)
  is-set-nonim = is-trunc-nonim neg-one-𝕋

nonim-Set :
  {l1 l2 : Level} (X : Set l1) {A : UU l2}
  (f : A → type-Set X) → Set (l1 ⊔ l2)
nonim-Set X f = nonim-Truncated-Type (neg-one-𝕋) X f
```

### The nonimage of a map into a 1-type is a 1-type

```agda
abstract
  is-1-type-nonim :
    {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
    is-1-type X → is-1-type (nonim f)
  is-1-type-nonim = is-trunc-nonim zero-𝕋

nonim-1-Type :
  {l1 l2 : Level} (X : 1-Type l1) {A : UU l2}
  (f : A → type-1-Type X) → 1-Type (l1 ⊔ l2)
nonim-1-Type X f = nonim-Truncated-Type zero-𝕋 X f
```
