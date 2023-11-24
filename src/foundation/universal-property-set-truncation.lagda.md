# The universal property of set truncations

```agda
module foundation.universal-property-set-truncation where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.mere-equality
open import foundation.reflecting-maps-equivalence-relations
open import foundation.sets
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-theoretic-principle-of-choice
open import foundation.universal-property-set-quotients
open import foundation.universe-levels

open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.functoriality-function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
```

</details>

## Idea

A map `f : A → B` into a [set](foundation-core.sets.md) `B` satisfies **the
universal property of the set truncation of `A`** if any map `A → C` into a set
`C` extends uniquely along `f` to a map `B → C`.

## Definition

### The condition for a map into a set to be a set truncation

```agda
is-set-truncation :
  ( l : Level) {l1 l2 : Level} {A : UU l1} (B : Set l2) →
  ( A → type-Set B) → UU (lsuc l ⊔ l1 ⊔ l2)
is-set-truncation l B f =
  (C : Set l) → is-equiv (precomp-Set f C)
```

### The universal property of set truncations

```agda
universal-property-set-truncation :
  ( l : Level) {l1 l2 : Level} {A : UU l1}
  (B : Set l2) (f : A → type-Set B) → UU (lsuc l ⊔ l1 ⊔ l2)
universal-property-set-truncation l {A = A} B f =
  (C : Set l) (g : A → type-Set C) →
  is-contr (Σ (hom-Set B C) (λ h → h ∘ f ~ g))
```

### The dependent universal property of set truncations

```agda
precomp-Π-Set :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : B → Set l3) →
  ((b : B) → type-Set (C b)) → ((a : A) → type-Set (C (f a)))
precomp-Π-Set f C h a = h (f a)

dependent-universal-property-set-truncation :
  {l1 l2 : Level} (l : Level) {A : UU l1} (B : Set l2) (f : A → type-Set B) →
  UU (l1 ⊔ l2 ⊔ lsuc l)
dependent-universal-property-set-truncation l B f =
  (X : type-Set B → Set l) → is-equiv (precomp-Π-Set f X)
```

## Properties

### A map into a set is a set truncation if it satisfies the universal property

```agda
abstract
  is-set-truncation-universal-property :
    (l : Level) {l1 l2 : Level} {A : UU l1}
    (B : Set l2) (f : A → type-Set B) →
    universal-property-set-truncation l B f →
    is-set-truncation l B f
  is-set-truncation-universal-property l B f up-f C =
    is-equiv-is-contr-map
      ( λ g → is-contr-equiv
        ( Σ (hom-Set B C) (λ h → h ∘ f ~ g))
        ( equiv-tot (λ h → equiv-funext))
        ( up-f C g))
```

### A map into a set satisfies the universal property if it is a set truncation

```agda
abstract
  universal-property-is-set-truncation :
    (l : Level) {l1 l2 : Level} {A : UU l1} (B : Set l2)
    (f : A → type-Set B) →
    is-set-truncation l B f → universal-property-set-truncation l B f
  universal-property-is-set-truncation l B f is-settr-f C g =
    is-contr-equiv'
      ( Σ (hom-Set B C) (λ h → (h ∘ f) ＝ g))
      ( equiv-tot (λ h → equiv-funext))
      ( is-contr-map-is-equiv (is-settr-f C) g)

map-is-set-truncation :
  {l1 l2 l3 : Level} {A : UU l1} (B : Set l2) (f : A → type-Set B) →
  ({l : Level} → is-set-truncation l B f) →
  (C : Set l3) (g : A → type-Set C) → hom-Set B C
map-is-set-truncation B f is-settr-f C g =
  pr1 (center (universal-property-is-set-truncation _ B f is-settr-f C g))

triangle-is-set-truncation :
  {l1 l2 l3 : Level} {A : UU l1} (B : Set l2) (f : A → type-Set B) →
  (is-settr-f : {l : Level} → is-set-truncation l B f) →
  (C : Set l3) (g : A → type-Set C) →
  map-is-set-truncation B f is-settr-f C g ∘ f ~ g
triangle-is-set-truncation B f is-settr-f C g =
  pr2 (center (universal-property-is-set-truncation _ B f is-settr-f C g))
```

### The identity function on any set is a set truncation

```agda
abstract
  is-set-truncation-id :
    {l1 l2 : Level} {A : UU l1} (H : is-set A) → is-set-truncation l2 (A , H) id
  is-set-truncation-id H B =
    is-equiv-precomp-is-equiv id is-equiv-id (type-Set B)
```

### Any equivalence into a set is a set truncation

```agda
abstract
  is-set-truncation-equiv :
    {l1 l2 : Level} {A : UU l1} (B : Set l2) (e : A ≃ type-Set B) →
    {l : Level} → is-set-truncation l B (map-equiv e)
  is-set-truncation-equiv B e C =
    is-equiv-precomp-is-equiv (map-equiv e) (is-equiv-map-equiv e) (type-Set C)
```

### Any set truncation satisfies the dependent universal property of the set truncation

```agda
abstract
  dependent-universal-property-is-set-truncation :
    {l1 l2 l3 : Level} {A : UU l1} (B : Set l2) (f : A → type-Set B) →
    ({l : Level} → is-set-truncation l B f) →
    dependent-universal-property-set-truncation l3 B f
  dependent-universal-property-is-set-truncation {A = A} B f H X =
    is-fiberwise-equiv-is-equiv-map-Σ
      ( λ (h : A → type-Set B) → (a : A) → type-Set (X (h a)))
      ( λ (g : type-Set B → type-Set B) → g ∘ f)
      ( λ g (s : (b : type-Set B) → type-Set (X (g b))) (a : A) → s (f a))
      ( H B)
      ( is-equiv-equiv
        ( inv-distributive-Π-Σ)
        ( inv-distributive-Π-Σ)
        ( ind-Σ (λ g s → refl))
        ( H (Σ-Set B X)))
      ( id)
```

### Any map satisfying the dependent universal property of set truncations is a set truncation

```agda
abstract
  is-set-truncation-dependent-universal-property :
    {l1 l2 l3 : Level} {A : UU l1} (B : Set l2) (f : A → type-Set B) →
    ({l : Level} → dependent-universal-property-set-truncation l B f) →
    is-set-truncation l3 B f
  is-set-truncation-dependent-universal-property B f H X =
    H (λ b → X)
```

### Any set quotient of the mere equality equivalence relation is a set truncation

```agda
abstract
  is-set-truncation-is-set-quotient :
    {l1 l2 l3 : Level} {A : UU l1} (B : Set l2) (f : A → type-Set B) →
    ( {l : Level} →
      is-set-quotient l
        ( mere-eq-equivalence-relation A)
        ( B)
        ( reflecting-map-mere-eq B f)) →
    is-set-truncation l3 B f
  is-set-truncation-is-set-quotient {A = A} B f H X =
    is-equiv-comp
      ( pr1)
      ( precomp-Set-Quotient
        ( mere-eq-equivalence-relation A)
        ( B)
        ( reflecting-map-mere-eq B f)
        ( X))
      ( H X)
      ( is-equiv-pr1-is-contr
        ( λ h →
          is-proof-irrelevant-is-prop
            ( is-prop-reflects-equivalence-relation
              ( mere-eq-equivalence-relation A) X h)
            ( reflects-mere-eq X h)))
```

### Any set truncation is a quotient of the mere equality equivalence relation

```agda
abstract
  is-set-quotient-is-set-truncation :
    {l1 l2 l3 : Level} {A : UU l1} (B : Set l2) (f : A → type-Set B) →
    ( {l : Level} → is-set-truncation l B f) →
    is-set-quotient l3
      ( mere-eq-equivalence-relation A)
      ( B)
      ( reflecting-map-mere-eq B f)
  is-set-quotient-is-set-truncation {A = A} B f H X =
    is-equiv-right-factor
      ( pr1)
      ( precomp-Set-Quotient
        ( mere-eq-equivalence-relation A)
        ( B)
        ( reflecting-map-mere-eq B f)
        ( X))
      ( is-equiv-pr1-is-contr
        ( λ h →
          is-proof-irrelevant-is-prop
            ( is-prop-reflects-equivalence-relation
              ( mere-eq-equivalence-relation A) X h)
            ( reflects-mere-eq X h)))
      ( H X)
```
