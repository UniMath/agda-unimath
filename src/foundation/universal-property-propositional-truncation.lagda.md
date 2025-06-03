# The universal property of propositional truncations

```agda
module foundation.universal-property-propositional-truncation where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.functoriality-cartesian-product-types
open import foundation.logical-equivalences
open import foundation.precomposition-functions-into-subuniverses
open import foundation.subtype-identity-principle
open import foundation.unit-type
open import foundation.universal-property-dependent-pair-types
open import foundation.universal-property-equivalences
open import foundation.universe-levels

open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.precomposition-dependent-functions
open import foundation-core.precomposition-functions
open import foundation-core.propositions
open import foundation-core.type-theoretic-principle-of-choice
```

</details>

## Idea

A map `f : A → P` into a [proposition](foundation-core.propositions.md) `P` is
said to satisfy the
{{#concept "universal property of the propositional truncation" Agda=universal-property-propositional-truncation}}
of `A`, or is said to be a
{{#concept "propositional truncation" Agda=is-propositional-truncation}} of `A`,
if any map `g : A → Q` into a proposition `Q` extends uniquely along `f`.

## Definition

### The condition of being a propositional truncation

```agda
module _
  {l1 l2 : Level} {A : UU l1} (P : Prop l2) (f : A → type-Prop P)
  where

  precomp-Prop :
    {l3 : Level} (Q : Prop l3) →
    type-hom-Prop P Q → A → type-Prop Q
  precomp-Prop Q g = g ∘ f

  is-propositional-truncation : UUω
  is-propositional-truncation =
    {l : Level} (Q : Prop l) → is-equiv (precomp-Prop Q)
```

### The universal property of the propositional truncation

```agda
module _
  {l1 l2 : Level} {A : UU l1}
  (P : Prop l2) (f : A → type-Prop P)
  where

  universal-property-propositional-truncation : UUω
  universal-property-propositional-truncation =
    {l : Level} (Q : Prop l) (g : A → type-Prop Q) →
    is-contr (Σ (type-hom-Prop P Q) (λ h → h ∘ f ~ g))
```

### Extension property of the propositional truncation

This is a simplified form of the universal properties, that works because we're
mapping into propositions.

```agda
module _
  {l1 l2 : Level} {A : UU l1}
  (P : Prop l2) (f : A → type-Prop P)
  where

  extension-property-propositional-truncation : UUω
  extension-property-propositional-truncation =
    {l : Level} (Q : Prop l) → (A → type-Prop Q) → type-hom-Prop P Q
```

### The dependent universal property of the propositional truncation

```agda
module _
  {l1 l2 : Level} {A : UU l1}
  (P : Prop l2) (f : A → type-Prop P)
  where

  dependent-universal-property-propositional-truncation : UUω
  dependent-universal-property-propositional-truncation =
    {l : Level} → (Q : type-Prop P → Prop l) →
    is-equiv (precomp-Π f (type-Prop ∘ Q))
```

## Properties

### Being a propositional truncation is equivalent to satisfying the universal property of the propositional truncation

```agda
abstract
  universal-property-is-propositional-truncation :
    {l1 l2 : Level} {A : UU l1} (P : Prop l2) (f : A → type-Prop P) →
    is-propositional-truncation P f →
    universal-property-propositional-truncation P f
  universal-property-is-propositional-truncation P f is-ptr-f Q g =
    is-contr-equiv'
      ( Σ (type-hom-Prop P Q) (λ h → h ∘ f ＝ g))
      ( equiv-tot (λ _ → equiv-funext))
      ( is-contr-map-is-equiv (is-ptr-f Q) g)

abstract
  map-is-propositional-truncation :
    {l1 l2 l3 : Level} {A : UU l1} (P : Prop l2) (f : A → type-Prop P) →
    is-propositional-truncation P f →
    (Q : Prop l3) (g : A → type-Prop Q) → type-hom-Prop P Q
  map-is-propositional-truncation P f is-ptr-f Q g =
    pr1
      ( center
        ( universal-property-is-propositional-truncation P f is-ptr-f Q g))

  htpy-is-propositional-truncation :
    {l1 l2 l3 : Level} {A : UU l1} (P : Prop l2) (f : A → type-Prop P) →
    (is-ptr-f : is-propositional-truncation P f) →
    (Q : Prop l3) (g : A → type-Prop Q) →
    map-is-propositional-truncation P f is-ptr-f Q g ∘ f ~ g
  htpy-is-propositional-truncation P f is-ptr-f Q g =
    pr2
      ( center
        ( universal-property-is-propositional-truncation P f is-ptr-f Q g))

abstract
  is-propositional-truncation-universal-property :
    {l1 l2 : Level} {A : UU l1}
    (P : Prop l2) (f : A → type-Prop P) →
    universal-property-propositional-truncation P f →
    is-propositional-truncation P f
  is-propositional-truncation-universal-property P f up-f Q =
    is-equiv-is-contr-map
      ( λ g → is-contr-equiv
        ( Σ (type-hom-Prop P Q) (λ h → (h ∘ f) ~ g))
        ( equiv-tot (λ h → equiv-funext))
        ( up-f Q g))
```

### Being a propositional truncation is equivalent to satisfying the extension property of propositional truncations

```agda
abstract
  is-propositional-truncation-extension-property :
    { l1 l2 : Level} {A : UU l1} (P : Prop l2)
    ( f : A → type-Prop P) →
    extension-property-propositional-truncation P f →
    is-propositional-truncation P f
  is-propositional-truncation-extension-property P f up-P Q =
    is-equiv-has-converse-is-prop
      ( is-prop-Π (λ x → is-prop-type-Prop Q))
      ( is-prop-Π (λ x → is-prop-type-Prop Q))
      ( up-P Q)
```

### Uniqueness of propositional truncations

```agda
abstract
  is-equiv-is-ptruncation-is-ptruncation :
    {l1 l2 l3 : Level} {A : UU l1} (P : Prop l2) (P' : Prop l3)
    (f : A → type-Prop P) (f' : A → type-Prop P')
    (h : type-hom-Prop P P') (H : (h ∘ f) ~ f') →
    is-propositional-truncation P f →
    is-propositional-truncation P' f' →
    is-equiv h
  is-equiv-is-ptruncation-is-ptruncation P P' f f' h H is-ptr-P is-ptr-P' =
    is-equiv-has-converse-is-prop
      ( is-prop-type-Prop P)
      ( is-prop-type-Prop P')
      ( map-inv-is-equiv (is-ptr-P' P) f)

abstract
  is-ptruncation-is-ptruncation-is-equiv :
    {l1 l2 l3 : Level} {A : UU l1} (P : Prop l2) (P' : Prop l3)
    (f : A → type-Prop P) (f' : A → type-Prop P') (h : type-hom-Prop P P') →
    is-equiv h → is-propositional-truncation P f →
    is-propositional-truncation P' f'
  is-ptruncation-is-ptruncation-is-equiv P P' f f' h is-equiv-h is-ptr-f =
    is-propositional-truncation-extension-property P' f'
      ( λ R g →
        ( map-is-propositional-truncation P f is-ptr-f R g) ∘
        ( map-inv-is-equiv is-equiv-h))

abstract
  is-ptruncation-is-equiv-is-ptruncation :
    {l1 l2 l3 : Level} {A : UU l1} (P : Prop l2) (P' : Prop l3)
    (f : A → type-Prop P) (f' : A → type-Prop P') (h : type-hom-Prop P P') →
    is-propositional-truncation P' f' → is-equiv h →
    is-propositional-truncation P f
  is-ptruncation-is-equiv-is-ptruncation P P' f f' h is-ptr-f' is-equiv-h =
    is-propositional-truncation-extension-property P f
      ( λ R g → (map-is-propositional-truncation P' f' is-ptr-f' R g) ∘ h)

abstract
  is-uniquely-unique-propositional-truncation :
    {l1 l2 l3 : Level} {A : UU l1} (P : Prop l2) (P' : Prop l3)
    (f : A → type-Prop P) (f' : A → type-Prop P') →
    is-propositional-truncation P f →
    is-propositional-truncation P' f' →
    is-contr (Σ (type-equiv-Prop P P') (λ e → (map-equiv e ∘ f) ~ f'))
  is-uniquely-unique-propositional-truncation P P' f f' is-ptr-f is-ptr-f' =
    is-torsorial-Eq-subtype
      ( universal-property-is-propositional-truncation P f is-ptr-f P' f')
      ( is-property-is-equiv)
      ( map-is-propositional-truncation P f is-ptr-f P' f')
      ( htpy-is-propositional-truncation P f is-ptr-f P' f')
      ( is-equiv-is-ptruncation-is-ptruncation P P' f f'
        ( map-is-propositional-truncation P f is-ptr-f P' f')
        ( htpy-is-propositional-truncation P f is-ptr-f P' f')
        ( λ {l} → is-ptr-f)
        ( λ {l} → is-ptr-f'))
```

### A map `f : A → P` is a propositional truncation if and only if it satisfies the dependent universal property of the propositional truncation

```agda
abstract
  dependent-universal-property-is-propositional-truncation :
    { l1 l2 : Level} {A : UU l1} (P : Prop l2) (f : A → type-Prop P) →
    is-propositional-truncation P f →
    dependent-universal-property-propositional-truncation P f
  dependent-universal-property-is-propositional-truncation
    {l1} {l2} {A} P f is-ptr-f Q =
    is-fiberwise-equiv-is-equiv-map-Σ
      ( λ (g : A → type-Prop P) → (x : A) → type-Prop (Q (g x)))
      ( precomp f (type-Prop P))
      ( λ h → precomp-Π f (λ p → type-Prop (Q (h p))))
      ( is-ptr-f P)
      ( is-equiv-top-is-equiv-bottom-square
        ( map-inv-distributive-Π-Σ
          { C = λ (x : type-Prop P) (p : type-Prop P) → type-Prop (Q p)})
        ( map-inv-distributive-Π-Σ
          { C = λ (x : A) (p : type-Prop P) → type-Prop (Q p)})
        ( map-Σ
          ( λ (g : A → type-Prop P) → (x : A) → type-Prop (Q (g x)))
          ( precomp f (type-Prop P))
          ( λ h → precomp-Π f (λ p → type-Prop (Q (h p)))))
        ( precomp f (Σ (type-Prop P) (λ p → type-Prop (Q p))))
        ( ind-Σ (λ h h' → refl))
        ( is-equiv-map-inv-distributive-Π-Σ)
        ( is-equiv-map-inv-distributive-Π-Σ)
        ( is-ptr-f (Σ-Prop P Q)))
      ( id {A = type-Prop P})

abstract
  is-propositional-truncation-dependent-universal-property :
    { l1 l2 : Level} {A : UU l1} (P : Prop l2) (f : A → type-Prop P) →
    dependent-universal-property-propositional-truncation P f →
    is-propositional-truncation P f
  is-propositional-truncation-dependent-universal-property P f dup-f Q =
    dup-f (λ p → Q)
```

### Any map `f : A → P` that has a section is a propositional truncation

```agda
abstract
  is-propositional-truncation-has-section :
    {l1 l2 : Level} {A : UU l1} (P : Prop l2) (f : A → type-Prop P) →
    (g : type-Prop P → A) → is-propositional-truncation P f
  is-propositional-truncation-has-section {A = A} P f g Q =
    is-equiv-has-converse-is-prop
      ( is-prop-function-type (is-prop-type-Prop Q))
      ( is-prop-function-type (is-prop-type-Prop Q))
      ( λ h → h ∘ g)
```

### If `A` is a pointed type, then the map `A → unit` is a propositional truncation

```agda
abstract
  is-propositional-truncation-terminal-map :
    { l1 : Level} (A : UU l1) (a : A) →
    is-propositional-truncation unit-Prop (terminal-map A)
  is-propositional-truncation-terminal-map A a =
    is-propositional-truncation-has-section
      ( unit-Prop)
      ( terminal-map A)
      ( ind-unit a)
```

### Any map between propositions is a propositional truncation if and only if it is an equivalence

```agda
abstract
  is-propositional-truncation-is-equiv :
    {l1 l2 : Level} (P : Prop l1) (Q : Prop l2)
    {f : type-hom-Prop P Q} →
    is-equiv f → is-propositional-truncation Q f
  is-propositional-truncation-is-equiv P Q {f} is-equiv-f R =
    is-equiv-precomp-is-equiv f is-equiv-f (type-Prop R)

abstract
  is-propositional-truncation-map-equiv :
    { l1 l2 : Level} (P : Prop l1) (Q : Prop l2)
    (e : type-equiv-Prop P Q) →
    is-propositional-truncation Q (map-equiv e)
  is-propositional-truncation-map-equiv P Q e R =
    is-equiv-precomp-is-equiv (map-equiv e) (is-equiv-map-equiv e) (type-Prop R)

abstract
  is-equiv-is-propositional-truncation :
    {l1 l2 : Level} (P : Prop l1) (Q : Prop l2) {f : type-hom-Prop P Q} →
    is-propositional-truncation Q f → is-equiv f
  is-equiv-is-propositional-truncation P Q {f} H =
    is-equiv-is-equiv-precomp-Prop P Q f H
```

### The identity map on a proposition is a propositional truncation

```agda
abstract
  is-propositional-truncation-id :
    { l1 : Level} (P : Prop l1) →
    is-propositional-truncation P id
  is-propositional-truncation-id P Q = is-equiv-id
```

### A product of propositional truncations is a propositional truncation

```agda
abstract
  is-propositional-truncation-product :
    {l1 l2 l3 l4 : Level}
    {A : UU l1} (P : Prop l2) (f : A → type-Prop P)
    {A' : UU l3} (P' : Prop l4) (f' : A' → type-Prop P') →
    is-propositional-truncation P f →
    is-propositional-truncation P' f' →
    is-propositional-truncation (product-Prop P P') (map-product f f')
  is-propositional-truncation-product P f P' f' is-ptr-f is-ptr-f' Q =
    is-equiv-top-is-equiv-bottom-square
      ( ev-pair)
      ( ev-pair)
      ( precomp (map-product f f') (type-Prop Q))
      ( λ h a a' → h (f a) (f' a'))
      ( refl-htpy)
      ( is-equiv-ev-pair)
      ( is-equiv-ev-pair)
      ( is-equiv-comp
        ( λ h a a' → h a (f' a'))
        ( λ h a p' → h (f a) p')
        ( is-ptr-f (pair (type-hom-Prop P' Q) (is-prop-hom-Prop P' Q)))
        ( is-equiv-map-Π-is-fiberwise-equiv
          ( λ a → is-ptr-f' Q)))
```
