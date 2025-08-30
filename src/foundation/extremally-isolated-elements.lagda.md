# Extremally isolated elements

```agda
module foundation.extremally-isolated-elements where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.constant-maps
open import foundation.decidable-embeddings
open import foundation.decidable-equality
open import foundation.decidable-maps
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.embeddings
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.isolated-elements
open import foundation.maybe
open import foundation.negated-equality
open import foundation.negation
open import foundation.sets
open import foundation.type-arithmetic-unit-type
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.coproduct-types
open import foundation-core.decidable-propositions
open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.propositions
open import foundation-core.subtypes
open import foundation-core.torsorial-type-families
open import foundation-core.transport-along-identifications

open import logic.de-morgan-maps
open import logic.de-morgan-types
```

</details>

## Idea

An element `a : A` is
{{#concept "extremally isolated" Agda=is-extremally-isolated Agda=extremally-extremally-isolated-element}}
if `a ＝ x` is [De Morgan](logic.de-morgan-types.md) for any `x`. I.e., if the
[proposition](foundation-core.propositions.md) `a ≠ x` is
[decidable](foundation-core.decidable-types.md).

## Definitions

### Extremally isolated elements

```agda
is-extremally-isolated :
  {l1 : Level} {X : UU l1} (a : X) → UU l1
is-extremally-isolated {l1} {X} a = (x : X) → is-decidable (a ≠ x)

extremally-isolated-element :
  {l1 : Level} (X : UU l1) → UU l1
extremally-isolated-element X = Σ X is-extremally-isolated

module _
  {l : Level} {X : UU l} (x : extremally-isolated-element X)
  where

  element-extremally-isolated-element : X
  element-extremally-isolated-element = pr1 x

  is-extremally-isolated-extremally-isolated-element :
    is-extremally-isolated element-extremally-isolated-element
  is-extremally-isolated-extremally-isolated-element = pr2 x
```

### Complements of extremally isolated elements

```agda
complement-extremally-isolated-element :
  {l1 : Level} (X : UU l1) → extremally-isolated-element X → UU l1
complement-extremally-isolated-element X x =
  Σ X (λ y → element-extremally-isolated-element x ≠ y)
```

## Properties

### Isolated elements are extremallly isolated

```agda
module _
  {l1 : Level} {X : UU l1}
  where

  is-extremally-isolated-is-isolated :
    (x : X) → is-isolated x → is-extremally-isolated x
  is-extremally-isolated-is-isolated x H y = is-de-morgan-is-decidable (H y)

  is-extremally-isolated-isolated-element :
    (x : isolated-element X) →
    is-extremally-isolated (element-isolated-element x)
  is-extremally-isolated-isolated-element (x , H) =
    is-extremally-isolated-is-isolated x H

  extremally-isolated-element-isolated-element :
    isolated-element X → extremally-isolated-element X
  extremally-isolated-element-isolated-element (x , H) =
    (x , is-extremally-isolated-isolated-element (x , H))
```

### An element is extremally isolated if and only if the constant map pointing at it is De Morgan

```agda
module _
  {l1 : Level} {A : UU l1} (a : A)
  where

  is-de-morgan-point-is-extremally-isolated :
    is-extremally-isolated a → is-de-morgan-map (point a)
  is-de-morgan-point-is-extremally-isolated d x =
    is-de-morgan-equiv (compute-fiber-point a x) (d x)

  is-extremally-isolated-is-de-morgan-point :
    is-de-morgan-map (point a) → is-extremally-isolated a
  is-extremally-isolated-is-de-morgan-point d x =
    is-de-morgan-equiv' (compute-fiber-point a x) (d x)
```

### Being an extremally isolated element is a property

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  is-prop-is-extremally-isolated : (a : A) → is-prop (is-extremally-isolated a)
  is-prop-is-extremally-isolated a =
    is-prop-Π (λ x → is-prop-is-de-morgan (a ＝ x))

  is-extremally-isolated-Prop : (a : A) → Prop l1
  pr1 (is-extremally-isolated-Prop a) = is-extremally-isolated a
  pr2 (is-extremally-isolated-Prop a) = is-prop-is-extremally-isolated a

  inclusion-extremally-isolated-element : extremally-isolated-element A → A
  inclusion-extremally-isolated-element = pr1

  is-emb-inclusion-extremally-isolated-element :
    is-emb inclusion-extremally-isolated-element
  is-emb-inclusion-extremally-isolated-element =
    is-emb-inclusion-subtype is-extremally-isolated-Prop

  has-decidable-equality-extremally-isolated-element :
    (u v : extremally-isolated-element A) → is-decidable (u ≠ v)
  has-decidable-equality-extremally-isolated-element (x , dx) (y , dy) =
    is-de-morgan-equiv
      ( equiv-ap-inclusion-subtype is-extremally-isolated-Prop)
      ( dx y)

module _
  {l1 : Level} {A : UU l1} (a : extremally-isolated-element A)
  where

  point-extremally-isolated-element : unit → A
  point-extremally-isolated-element =
    point (element-extremally-isolated-element a)

  is-de-morgan-point-extremally-isolated-element :
    is-de-morgan-map point-extremally-isolated-element
  is-de-morgan-point-extremally-isolated-element =
    is-de-morgan-point-is-extremally-isolated
      ( element-extremally-isolated-element a)
      ( is-extremally-isolated-extremally-isolated-element a)
```

## See also

- [Isolated elements](foundation.isolated-elements.md)
