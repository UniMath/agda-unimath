# Isolated elements

```agda
module foundation.isolated-elements where
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
open import foundation.dependent-products-propositions
open import foundation.embeddings
open import foundation.equivalences-contractible-types
open import foundation.full-subtypes
open import foundation.functoriality-coproduct-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.negated-equality
open import foundation.negation
open import foundation.sets
open import foundation.type-arithmetic-coproduct-types
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
open import foundation-core.maybe
open import foundation-core.propositions
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.subtypes
open import foundation-core.torsorial-type-families
open import foundation-core.transport-along-identifications
```

</details>

## Idea

An element `a : A` is
{{#concept "isolated" Disambiguation="element of a type" Agda=is-isolated Agda=isolated-element}}
if `a ＝ x` is [decidable](foundation.decidable-types.md) for any `x`.

## Definitions

### Isolated elements

```agda
is-isolated :
  {l1 : Level} {A : UU l1} (a : A) → UU l1
is-isolated {l1} {A} a = (x : A) → is-decidable (a ＝ x)

isolated-element :
  {l1 : Level} (A : UU l1) → UU l1
isolated-element A = Σ A is-isolated

module _
  {l : Level} {A : UU l} (a : isolated-element A)
  where

  element-isolated-element : A
  element-isolated-element = pr1 a

  inclusion-isolated-element : A
  inclusion-isolated-element = element-isolated-element

  is-isolated-isolated-element : is-isolated element-isolated-element
  is-isolated-isolated-element = pr2 a
```

### Complements of isolated elements

```agda
module _
  {l1 : Level} {A : UU l1} (a : isolated-element A)
  where

  is-in-complement-isolated-element :
    A → UU l1
  is-in-complement-isolated-element x =
    element-isolated-element a ≠ x

  is-prop-is-in-complement-isolated-element :
    (x : A) → is-prop (is-in-complement-isolated-element x)
  is-prop-is-in-complement-isolated-element x =
    is-prop-neg

  is-in-complement-prop-isolated-element :
    subtype l1 A
  pr1 (is-in-complement-prop-isolated-element x) =
    is-in-complement-isolated-element x
  pr2 (is-in-complement-prop-isolated-element x) =
    is-prop-is-in-complement-isolated-element x

  complement-isolated-element :
    UU l1
  complement-isolated-element =
    type-subtype is-in-complement-prop-isolated-element

  inclusion-complement-isolated-element :
    complement-isolated-element → A
  inclusion-complement-isolated-element = pr1
```

## Properties

### Characterization of equality of the type of isolated elements

```agda
module _
  {l1 : Level} {A : UU l1} (a : A)
  where

  cases-Eq-isolated-element :
    is-isolated a → (x : A) → is-decidable (a ＝ x) → UU lzero
  cases-Eq-isolated-element H x (inl p) = unit
  cases-Eq-isolated-element H x (inr f) = empty

  abstract
    is-prop-cases-Eq-isolated-element :
      (d : is-isolated a) (x : A) (dx : is-decidable (a ＝ x)) →
      is-prop (cases-Eq-isolated-element d x dx)
    is-prop-cases-Eq-isolated-element d x (inl p) = is-prop-unit
    is-prop-cases-Eq-isolated-element d x (inr f) = is-prop-empty

  Eq-isolated-element : is-isolated a → A → UU lzero
  Eq-isolated-element d x = cases-Eq-isolated-element d x (d x)

  abstract
    is-prop-Eq-isolated-element :
      (d : is-isolated a) (x : A) → is-prop (Eq-isolated-element d x)
    is-prop-Eq-isolated-element d x =
      is-prop-cases-Eq-isolated-element d x (d x)

  Eq-isolated-element-Prop : is-isolated a → A → Prop lzero
  pr1 (Eq-isolated-element-Prop d x) = Eq-isolated-element d x
  pr2 (Eq-isolated-element-Prop d x) = is-prop-Eq-isolated-element d x

  decide-reflexivity :
    (d : is-decidable (a ＝ a)) → Σ (a ＝ a) (λ p → inl p ＝ d)
  pr1 (decide-reflexivity (inl p)) = p
  pr2 (decide-reflexivity (inl p)) = refl
  decide-reflexivity (inr f) = ex-falso (f refl)

  abstract
    refl-Eq-isolated-element : (d : is-isolated a) → Eq-isolated-element d a
    refl-Eq-isolated-element d =
      tr
        ( cases-Eq-isolated-element d a)
        ( pr2 (decide-reflexivity (d a)))
        ( star)

  abstract
    Eq-eq-isolated-element :
      (d : is-isolated a) {x : A} → a ＝ x → Eq-isolated-element d x
    Eq-eq-isolated-element d refl = refl-Eq-isolated-element d

  abstract
    center-total-Eq-isolated-element :
      (d : is-isolated a) → Σ A (Eq-isolated-element d)
    pr1 (center-total-Eq-isolated-element d) = a
    pr2 (center-total-Eq-isolated-element d) = refl-Eq-isolated-element d

    cases-contraction-total-Eq-isolated-element :
      (d : is-isolated a) (x : A) (dx : is-decidable (a ＝ x))
      (e : cases-Eq-isolated-element d x dx) → a ＝ x
    cases-contraction-total-Eq-isolated-element d x (inl p) e = p

    contraction-total-Eq-isolated-element :
      (d : is-isolated a) (t : Σ A (Eq-isolated-element d)) →
      center-total-Eq-isolated-element d ＝ t
    contraction-total-Eq-isolated-element d (x , e) =
      eq-type-subtype
        ( Eq-isolated-element-Prop d)
        ( cases-contraction-total-Eq-isolated-element d x (d x) e)

    is-torsorial-Eq-isolated-element :
      (d : is-isolated a) → is-torsorial (Eq-isolated-element d)
    pr1 (is-torsorial-Eq-isolated-element d) =
      center-total-Eq-isolated-element d
    pr2 (is-torsorial-Eq-isolated-element d) =
      contraction-total-Eq-isolated-element d

  abstract
    is-equiv-Eq-eq-isolated-element :
      (d : is-isolated a) (x : A) → is-equiv (Eq-eq-isolated-element d {x})
    is-equiv-Eq-eq-isolated-element d =
      fundamental-theorem-id
        ( is-torsorial-Eq-isolated-element d)
        ( λ x → Eq-eq-isolated-element d {x})

  abstract
    equiv-Eq-eq-isolated-element :
      (d : is-isolated a) (x : A) → (a ＝ x) ≃ Eq-isolated-element d x
    pr1 (equiv-Eq-eq-isolated-element d x) = Eq-eq-isolated-element d
    pr2 (equiv-Eq-eq-isolated-element d x) = is-equiv-Eq-eq-isolated-element d x

  abstract
    is-prop-eq-isolated-element : (d : is-isolated a) (x : A) → is-prop (a ＝ x)
    is-prop-eq-isolated-element d x =
      is-prop-equiv
        ( equiv-Eq-eq-isolated-element d x)
        ( is-prop-Eq-isolated-element d x)

module _
  {l1 : Level} {A : UU l1} ((a , d) : isolated-element A)
  where

  eq-isolated-element-Prop :
    subtype l1 A
  pr1 (eq-isolated-element-Prop x) = a ＝ x
  pr2 (eq-isolated-element-Prop x) = is-prop-eq-isolated-element a d x
```

### The loop space at an isolated element is contractible

```agda
module _
  {l1 : Level} {A : UU l1} (a : A)
  where

  is-contr-loop-space-isolated-element :
    (d : is-isolated a) → is-contr (a ＝ a)
  is-contr-loop-space-isolated-element d =
    is-proof-irrelevant-is-prop (is-prop-eq-isolated-element a d a) refl
```

### An element is isolated if and only if its point inclusion is decidable

```agda
module _
  {l1 : Level} {A : UU l1} {a : A}
  where

  is-decidable-point-is-isolated :
    is-isolated a → is-decidable-map (point a)
  is-decidable-point-is-isolated d x =
    is-decidable-equiv (compute-fiber-point a x) (d x)

  is-isolated-is-decidable-point :
    is-decidable-map (point a) → is-isolated a
  is-isolated-is-decidable-point d x =
    is-decidable-equiv' (compute-fiber-point a x) (d x)
```

### The point inclusion of an isolated element is a decidable embedding

```agda
module _
  {l1 : Level} {A : UU l1} {a : A}
  where

  abstract
    is-emb-point-is-isolated : is-isolated a → is-emb (point a)
    is-emb-point-is-isolated d star =
      fundamental-theorem-id
        ( is-contr-equiv
          ( a ＝ a)
          ( left-unit-law-product)
          ( is-proof-irrelevant-is-prop
            ( is-prop-eq-isolated-element a d a)
            ( refl)))
        ( λ x → ap (λ y → a))

  abstract
    is-decidable-emb-point-is-isolated :
      is-isolated a → is-decidable-emb (point a)
    pr1 (is-decidable-emb-point-is-isolated d) =
      is-emb-point-is-isolated d
    pr2 (is-decidable-emb-point-is-isolated d) =
      is-decidable-point-is-isolated d
```

### Being an isolated element is a property

```agda
is-prop-is-isolated :
  {l1 : Level} {A : UU l1} (a : A) → is-prop (is-isolated a)
is-prop-is-isolated a =
  is-prop-has-element
    ( λ H → is-prop-Π (is-prop-is-decidable ∘ is-prop-eq-isolated-element a H))

is-isolated-Prop :
  {l1 : Level} {A : UU l1} (a : A) → Prop l1
pr1 (is-isolated-Prop a) = is-isolated a
pr2 (is-isolated-Prop a) = is-prop-is-isolated a
```

### The inclusion of the isolated elements into the ambient type is an embedding

```agda
is-emb-inclusion-isolated-element :
  {l1 : Level} (A : UU l1) → is-emb (inclusion-isolated-element {A = A})
is-emb-inclusion-isolated-element A = is-emb-inclusion-subtype is-isolated-Prop
```

### The type of isolated elements has decidable equality

```agda
has-decidable-equality-isolated-element :
  {l1 : Level} (A : UU l1) → has-decidable-equality (isolated-element A)
has-decidable-equality-isolated-element A (x , dx) (y , dy) =
  is-decidable-equiv
    ( equiv-ap-inclusion-subtype is-isolated-Prop)
    ( dx y)
```

### The type of isolated elements is a set

```agda
is-set-isolated-element :
  {l1 : Level} (A : UU l1) → is-set (isolated-element A)
is-set-isolated-element A =
  is-set-has-decidable-equality (has-decidable-equality-isolated-element A)
```

### The point inclusion of an isolated element

```agda
module _
  {l1 : Level} {A : UU l1} (a : isolated-element A)
  where

  point-isolated-element : unit → A
  point-isolated-element = point (element-isolated-element a)

  is-emb-point-isolated-element : is-emb point-isolated-element
  is-emb-point-isolated-element =
    is-emb-comp
      ( inclusion-isolated-element)
      ( point a)
      ( is-emb-inclusion-isolated-element A)
      ( is-emb-is-injective
        ( is-set-isolated-element A)
        ( λ p → refl))

  emb-point-isolated-element : unit ↪ A
  pr1 emb-point-isolated-element = point-isolated-element
  pr2 emb-point-isolated-element = is-emb-point-isolated-element

  is-decidable-point-isolated-element :
    is-decidable-map point-isolated-element
  is-decidable-point-isolated-element x =
    is-decidable-product is-decidable-unit (is-isolated-isolated-element a x)

  is-decidable-emb-point-isolated-element :
    is-decidable-emb point-isolated-element
  pr1 is-decidable-emb-point-isolated-element =
    is-emb-point-isolated-element
  pr2 is-decidable-emb-point-isolated-element =
    is-decidable-point-isolated-element

  decidable-emb-point-isolated-element : unit ↪ᵈ A
  pr1 decidable-emb-point-isolated-element =
    point-isolated-element
  pr2 decidable-emb-point-isolated-element =
    is-decidable-emb-point-isolated-element
```

### If `a` is an isolated element, then the type `Σ (x : A) ((a ＝ x) + (a ≠ x))` is equivalent to `A`

We define the
{{#concept "split full subtype" Disambiguation="isolated element" Agda=split-full-subtype-isolated-element}}
associated to an isolated element as the [subtype](foundation-core.subtypes.md)
consisting of all elements `x` satisfying the proposition `(a ＝ x) + (a ≠ x)`.
This subtype is [full](foundation.full-subtypes.md) since `a` is assumed to be
an isolated element.

```agda
module _
  {l1 : Level} {A : UU l1} ((a , d) : isolated-element A)
  where

  is-in-split-full-subtype-isolated-element :
    A → UU l1
  is-in-split-full-subtype-isolated-element x =
    (a ＝ x) + (a ≠ x)

  is-prop-is-in-split-full-subtype-isolated-element :
    (x : A) → is-prop (is-in-split-full-subtype-isolated-element x)
  is-prop-is-in-split-full-subtype-isolated-element x =
    is-prop-is-decidable (is-prop-eq-isolated-element a d x)

  split-full-subtype-isolated-element :
    subtype l1 A
  pr1 (split-full-subtype-isolated-element x) =
    is-in-split-full-subtype-isolated-element x
  pr2 (split-full-subtype-isolated-element x) =
    is-prop-is-in-split-full-subtype-isolated-element x

  type-split-full-subtype-isolated-element :
    UU l1
  type-split-full-subtype-isolated-element =
    type-subtype split-full-subtype-isolated-element

  compute-type-split-full-subtype-isolated-element :
    type-split-full-subtype-isolated-element ≃ A
  compute-type-split-full-subtype-isolated-element =
    equiv-inclusion-is-full-subtype split-full-subtype-isolated-element d
```

### Types with isolated elements can be equipped with a Maybe-structure

```agda
module _
  {l1 : Level} {X : UU l1} ((x , d) : isolated-element X)
  where

  map-maybe-structure-isolated-element :
    Maybe (complement-isolated-element (x , d)) → X
  map-maybe-structure-isolated-element (inl (y , f)) = y
  map-maybe-structure-isolated-element (inr star) = x

  cases-map-inv-maybe-structure-isolated-element :
    (y : X) → is-decidable (x ＝ y) →
    Maybe (complement-isolated-element (x , d))
  cases-map-inv-maybe-structure-isolated-element y (inl p) =
    inr star
  cases-map-inv-maybe-structure-isolated-element y (inr f) =
    inl (y , f)

  map-inv-maybe-structure-isolated-element :
    X → Maybe (complement-isolated-element (x , d))
  map-inv-maybe-structure-isolated-element y =
    cases-map-inv-maybe-structure-isolated-element y (d y)

  cases-is-section-map-inv-maybe-structure-isolated-element :
    (y : X) (d : is-decidable (x ＝ y)) →
    ( map-maybe-structure-isolated-element
      ( cases-map-inv-maybe-structure-isolated-element y d)) ＝
    ( y)
  cases-is-section-map-inv-maybe-structure-isolated-element .x (inl refl) =
    refl
  cases-is-section-map-inv-maybe-structure-isolated-element y (inr f) =
    refl

  is-section-map-inv-maybe-structure-isolated-element :
    ( map-maybe-structure-isolated-element ∘
      map-inv-maybe-structure-isolated-element) ~ id
  is-section-map-inv-maybe-structure-isolated-element y =
    cases-is-section-map-inv-maybe-structure-isolated-element y (d y)

  is-retraction-map-inv-maybe-structure-isolated-element :
    ( map-inv-maybe-structure-isolated-element ∘
      map-maybe-structure-isolated-element) ~ id
  is-retraction-map-inv-maybe-structure-isolated-element (inl (y , f)) =
    ap
      ( cases-map-inv-maybe-structure-isolated-element y)
      ( eq-is-prop (is-prop-is-decidable (is-prop-eq-isolated-element x d y)))
  is-retraction-map-inv-maybe-structure-isolated-element (inr star) =
    ap
      ( cases-map-inv-maybe-structure-isolated-element x)
      { x = d (map-maybe-structure-isolated-element (inr star))}
      { y = inl refl}
      ( eq-is-prop (is-prop-is-decidable (is-prop-eq-isolated-element x d x)))

  is-equiv-map-maybe-structure-isolated-element :
    is-equiv (map-maybe-structure-isolated-element)
  is-equiv-map-maybe-structure-isolated-element =
    is-equiv-is-invertible
      ( map-inv-maybe-structure-isolated-element)
      ( is-section-map-inv-maybe-structure-isolated-element)
      ( is-retraction-map-inv-maybe-structure-isolated-element)

  equiv-maybe-structure-isolated-element :
    Maybe (complement-isolated-element (x , d)) ≃ X
  pr1 (equiv-maybe-structure-isolated-element) =
    map-maybe-structure-isolated-element
  pr2 (equiv-maybe-structure-isolated-element) =
    is-equiv-map-maybe-structure-isolated-element

  maybe-structure-isolated-element :
    maybe-structure X
  pr1 maybe-structure-isolated-element =
    complement-isolated-element (x , d)
  pr2 maybe-structure-isolated-element =
    equiv-maybe-structure-isolated-element
```

## See also

- [Automorphism decompositions with respect to isolated elements](foundation.automorphism-decompositions-isolated-elements.md)
- [Equivalences between types with isolated elements](foundation.equivalences-types-with-isolated-elements.md)
- [Transpositions at isolated elements](foundation.transpositions-isolated-elements.md)
