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
open import foundation.embeddings
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.injective-maps
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
  {l1 : Level} {X : UU l1} (a : X) → UU l1
is-isolated {l1} {X} a = (x : X) → is-decidable (a ＝ x)

isolated-element :
  {l1 : Level} (X : UU l1) → UU l1
isolated-element X = Σ X is-isolated

module _
  {l : Level} {X : UU l} (x : isolated-element X)
  where

  element-isolated-element : X
  element-isolated-element = pr1 x

  is-isolated-isolated-element : is-isolated element-isolated-element
  is-isolated-isolated-element = pr2 x
```

### Complements of isolated elements

```agda
complement-isolated-element :
  {l1 : Level} (X : UU l1) → isolated-element X → UU l1
complement-isolated-element X x =
  Σ X (λ y → element-isolated-element x ≠ y)
```

## Properties

### An element is isolated if and only if the constant map pointing at it is decidable

```agda
module _
  {l1 : Level} {A : UU l1} (a : A)
  where

  is-decidable-point-is-isolated :
    is-isolated a → is-decidable-map (point a)
  is-decidable-point-is-isolated d x =
    is-decidable-equiv (compute-fiber-point a x) (d x)

  is-isolated-is-decidable-point :
    is-decidable-map (point a) → is-isolated a
  is-isolated-is-decidable-point d x =
    is-decidable-equiv' (compute-fiber-point a x) (d x)

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

  is-contr-loop-space-isolated-element :
    (d : is-isolated a) → is-contr (a ＝ a)
  is-contr-loop-space-isolated-element d =
    is-proof-irrelevant-is-prop (is-prop-eq-isolated-element d a) refl

  abstract
    is-emb-point-is-isolated : is-isolated a → is-emb (point a)
    is-emb-point-is-isolated d star =
      fundamental-theorem-id
        ( is-contr-equiv
          ( a ＝ a)
          ( left-unit-law-product)
          ( is-proof-irrelevant-is-prop
            ( is-prop-eq-isolated-element d a)
            ( refl)))
        ( λ x → ap (λ y → a))
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

inclusion-isolated-element :
  {l1 : Level} (A : UU l1) → isolated-element A → A
inclusion-isolated-element A = pr1

is-emb-inclusion-isolated-element :
  {l1 : Level} (A : UU l1) → is-emb (inclusion-isolated-element A)
is-emb-inclusion-isolated-element A = is-emb-inclusion-subtype is-isolated-Prop

has-decidable-equality-isolated-element :
  {l1 : Level} (A : UU l1) → has-decidable-equality (isolated-element A)
has-decidable-equality-isolated-element A (x , dx) (y , dy) =
  is-decidable-equiv
    ( equiv-ap-inclusion-subtype is-isolated-Prop)
    ( dx y)

is-set-isolated-element :
  {l1 : Level} (A : UU l1) → is-set (isolated-element A)
is-set-isolated-element A =
  is-set-has-decidable-equality (has-decidable-equality-isolated-element A)

module _
  {l1 : Level} {A : UU l1} (a : isolated-element A)
  where

  point-isolated-element : unit → A
  point-isolated-element = point (element-isolated-element a)

  is-emb-point-isolated-element : is-emb point-isolated-element
  is-emb-point-isolated-element =
    is-emb-comp
      ( inclusion-isolated-element A)
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

### Types with isolated elements can be equipped with a Maybe-structure

```agda
map-maybe-structure-isolated-element :
  {l1 : Level} (X : UU l1) (x : isolated-element X) →
  Maybe (complement-isolated-element X x) → X
map-maybe-structure-isolated-element X (x , d) (inl (y , f)) = y
map-maybe-structure-isolated-element X (x , d) (inr star) = x

cases-map-inv-maybe-structure-isolated-element :
  {l1 : Level} (X : UU l1) (x : isolated-element X) →
  (y : X) → is-decidable (pr1 x ＝ y) → Maybe (complement-isolated-element X x)
cases-map-inv-maybe-structure-isolated-element X (x , dx) y (inl p) =
  inr star
cases-map-inv-maybe-structure-isolated-element X (x , dx) y (inr f) =
  inl (y , f)

map-inv-maybe-structure-isolated-element :
  {l1 : Level} (X : UU l1) (x : isolated-element X) →
  X → Maybe (complement-isolated-element X x)
map-inv-maybe-structure-isolated-element X (x , d) y =
  cases-map-inv-maybe-structure-isolated-element X (x , d) y (d y)

cases-is-section-map-inv-maybe-structure-isolated-element :
  {l1 : Level} (X : UU l1) (x : isolated-element X) →
  (y : X) (d : is-decidable (pr1 x ＝ y)) →
  ( map-maybe-structure-isolated-element X x
    ( cases-map-inv-maybe-structure-isolated-element X x y d)) ＝
  ( y)
cases-is-section-map-inv-maybe-structure-isolated-element X
  (x , dx) .x (inl refl) =
  refl
cases-is-section-map-inv-maybe-structure-isolated-element X (x , dx) y (inr f) =
  refl

is-section-map-inv-maybe-structure-isolated-element :
  {l1 : Level} (X : UU l1) (x : isolated-element X) →
  ( map-maybe-structure-isolated-element X x ∘
    map-inv-maybe-structure-isolated-element X x) ~ id
is-section-map-inv-maybe-structure-isolated-element X (x , d) y =
  cases-is-section-map-inv-maybe-structure-isolated-element X (x , d) y (d y)

is-retraction-map-inv-maybe-structure-isolated-element :
  {l1 : Level} (X : UU l1) (x : isolated-element X) →
  ( map-inv-maybe-structure-isolated-element X x ∘
    map-maybe-structure-isolated-element X x) ~ id
is-retraction-map-inv-maybe-structure-isolated-element
  X (x , dx) (inl (y , f)) =
  ap
    ( cases-map-inv-maybe-structure-isolated-element X (x , dx) y)
    ( eq-is-prop (is-prop-is-decidable (is-prop-eq-isolated-element x dx y)))
is-retraction-map-inv-maybe-structure-isolated-element X (x , dx) (inr star) =
  ap
    ( cases-map-inv-maybe-structure-isolated-element X (x , dx) x)
    { x = dx (map-maybe-structure-isolated-element X (x , dx) (inr star))}
    { y = inl refl}
    ( eq-is-prop (is-prop-is-decidable (is-prop-eq-isolated-element x dx x)))

is-equiv-map-maybe-structure-isolated-element :
  {l1 : Level} (X : UU l1) (x : isolated-element X) →
  is-equiv (map-maybe-structure-isolated-element X x)
is-equiv-map-maybe-structure-isolated-element X x =
  is-equiv-is-invertible
    ( map-inv-maybe-structure-isolated-element X x)
    ( is-section-map-inv-maybe-structure-isolated-element X x)
    ( is-retraction-map-inv-maybe-structure-isolated-element X x)

equiv-maybe-structure-isolated-element :
  {l1 : Level} (X : UU l1) (x : isolated-element X) →
  Maybe (complement-isolated-element X x) ≃ X
pr1 (equiv-maybe-structure-isolated-element X x) =
  map-maybe-structure-isolated-element X x
pr2 (equiv-maybe-structure-isolated-element X x) =
  is-equiv-map-maybe-structure-isolated-element X x

maybe-structure-isolated-element :
  {l1 : Level} {X : UU l1} → isolated-element X → maybe-structure X
pr1 (maybe-structure-isolated-element {l1} {X} x) =
  complement-isolated-element X x
pr2 (maybe-structure-isolated-element {l1} {X} x) =
  equiv-maybe-structure-isolated-element X x
```

```agda
equiv-complement-isolated-element :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : X ≃ Y) (x : isolated-element X)
  (y : isolated-element Y) (p : map-equiv e (pr1 x) ＝ pr1 y) →
  complement-isolated-element X x ≃ complement-isolated-element Y y
equiv-complement-isolated-element e x y p =
  equiv-Σ
    ( λ z → pr1 y ≠ z)
    ( e)
    ( λ z →
      equiv-neg
        ( equiv-concat (inv p) (map-equiv e z) ∘e (equiv-ap e (pr1 x) z)))
```

```agda
inclusion-complement-isolated-element :
  {l1 : Level} {X : UU l1} (x : isolated-element X) →
  complement-isolated-element X x → X
inclusion-complement-isolated-element x = pr1

natural-inclusion-equiv-complement-isolated-element :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : X ≃ Y) (x : isolated-element X)
  (y : isolated-element Y) (p : map-equiv e (pr1 x) ＝ pr1 y) →
  ( inclusion-complement-isolated-element y ∘
    map-equiv (equiv-complement-isolated-element e x y p)) ~
  ( map-equiv e ∘ inclusion-complement-isolated-element x)
natural-inclusion-equiv-complement-isolated-element e x y p (x' , f) = refl
```
