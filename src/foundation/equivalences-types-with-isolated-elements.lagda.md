# Equivalences between types with isolated elements

```agda
module foundation.equivalences-types-with-isolated-elements where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-maps
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalence-extensionality
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.isolated-elements
open import foundation.negated-equality
open import foundation.negation
open import foundation.propositions
open import foundation.retractions
open import foundation.sections
open import foundation.subtype-identity-principle
open import foundation.torsorial-type-families
open import foundation.transposition-identifications-along-equivalences
open import foundation.universe-levels

open import foundation-core.coproduct-types
open import foundation-core.equivalences
open import foundation-core.homotopies
open import foundation-core.logical-equivalences
open import foundation-core.subtypes

open import structured-types.pointed-equivalences
```

</details>

## Idea

Consider an [equivalence](foundation-core.equivalences.md) `e : A ≃ B`. Then `e`
maps [isolated elements](foundation.isolated-elements.md) in `A` to isolated
elements in `B`. This way, the equivalence `e` induces an equivalence

```text
  isolated-element A ≃ isolated-element B.
```

## Definitions

### Functoriality of `isolated-element`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B)
  where

  abstract
    preserves-isolated-elements-equiv :
      {a : A} → is-isolated a → is-isolated (map-equiv e a)
    preserves-isolated-elements-equiv d y =
      map-coproduct
        ( λ p → ap (map-equiv e) p ∙ is-section-map-inv-equiv e y)
        ( λ f → f ∘ map-eq-transpose-equiv e)
        ( d (map-inv-equiv e y))

  abstract
    reflects-isolated-elements-equiv :
      {a : A} → is-isolated (map-equiv e a) → is-isolated a
    reflects-isolated-elements-equiv d x =
      map-coproduct
        ( is-injective-equiv e)
        ( λ f → f ∘ ap (map-equiv e))
        ( d (map-equiv e x))

  preserves-and-reflects-isolated-elements-equiv :
    (a : A) → is-isolated a ↔ is-isolated (map-equiv e a)
  pr1 (preserves-and-reflects-isolated-elements-equiv a) =
    preserves-isolated-elements-equiv
  pr2 (preserves-and-reflects-isolated-elements-equiv a) =
    reflects-isolated-elements-equiv

  equiv-isolated-element :
    isolated-element A ≃ isolated-element B
  equiv-isolated-element =
    equiv-subtype-equiv e
      ( is-isolated-Prop)
      ( is-isolated-Prop)
      ( preserves-and-reflects-isolated-elements-equiv)

  map-equiv-isolated-element :
    isolated-element A → isolated-element B
  map-equiv-isolated-element =
    map-equiv equiv-isolated-element
```

### Functoriality of the complement of an isolated element

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  ((a , d) : isolated-element A) ((b , c) : isolated-element B)
  ((e , p) : (A , a) ≃∗ (B , b))
  where

  equiv-complement-isolated-element :
    complement-isolated-element (a , d) ≃ complement-isolated-element (b , c)
  equiv-complement-isolated-element =
    equiv-Σ
      ( is-in-complement-isolated-element (b , c))
      ( e)
      ( λ x →
        equiv-neg
          ( equiv-concat (inv p) (map-equiv e x) ∘e
            equiv-ap e (element-isolated-element (a , d)) x))

  map-equiv-complement-isolated-element :
    complement-isolated-element (a , d) → complement-isolated-element (b , c)
  map-equiv-complement-isolated-element =
    map-equiv equiv-complement-isolated-element

  natural-inclusion-equiv-complement-isolated-element :
    coherence-square-maps
      ( inclusion-complement-isolated-element (a , d))
      ( map-equiv equiv-complement-isolated-element)
      ( map-equiv e)
      ( inclusion-complement-isolated-element (b , c))
  natural-inclusion-equiv-complement-isolated-element (x , f) = refl
```

### The extension of an equivalence between the complements of isolated elements to a pointed equivalence

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  ((a , d) : isolated-element A) ((b , c) : isolated-element B)
  (e :
    complement-isolated-element (a , d) ≃ complement-isolated-element (b , c))
  where

  cases-map-extension-equiv-complement-isolated-element :
    (x : A) → is-decidable (a ＝ x) → B
  cases-map-extension-equiv-complement-isolated-element x (inl p) =
    b
  cases-map-extension-equiv-complement-isolated-element x (inr n) =
    inclusion-complement-isolated-element (b , c) (map-equiv e (x , n))

  map-extension-equiv-complement-isolated-element : A → B
  map-extension-equiv-complement-isolated-element x =
    cases-map-extension-equiv-complement-isolated-element x (d x)

  cases-compute-map-extension-equiv-complement-isolated-element :
    (x : A) (u : is-decidable (a ＝ x))
    (n : is-in-complement-isolated-element (a , d) x) →
    cases-map-extension-equiv-complement-isolated-element x u ＝
    pr1 (map-equiv e (x , n))
  cases-compute-map-extension-equiv-complement-isolated-element x (inl p) n =
    ex-falso (n p)
  cases-compute-map-extension-equiv-complement-isolated-element x (inr m) n =
    ap (λ t → pr1 (map-equiv e (x , t))) (eq-is-prop is-prop-neg)

  compute-map-extension-equiv-complement-isolated-element :
    (x : A) (n : is-in-complement-isolated-element (a , d) x) →
    map-extension-equiv-complement-isolated-element x ＝
    pr1 (map-equiv e (x , n))
  compute-map-extension-equiv-complement-isolated-element x n =
    cases-compute-map-extension-equiv-complement-isolated-element x (d x) n

  cases-map-inv-extension-equiv-complement-isolated-element :
    (y : B) → is-decidable (b ＝ y) → A
  cases-map-inv-extension-equiv-complement-isolated-element y (inl q) = a
  cases-map-inv-extension-equiv-complement-isolated-element y (inr n) =
    inclusion-complement-isolated-element (a , d) (map-inv-equiv e (y , n))

  map-inv-extension-equiv-complement-isolated-element :
    B → A
  map-inv-extension-equiv-complement-isolated-element y =
    cases-map-inv-extension-equiv-complement-isolated-element y (c y)

  cases-is-section-map-inv-extension-equiv-complement-isolated-element :
    (y : B) (v : is-decidable (b ＝ y))
    (u :
      is-decidable
        ( a ＝ cases-map-inv-extension-equiv-complement-isolated-element y v)) →
    cases-map-extension-equiv-complement-isolated-element
      ( cases-map-inv-extension-equiv-complement-isolated-element y v)
      ( u) ＝
    y
  cases-is-section-map-inv-extension-equiv-complement-isolated-element y
    ( inl refl) (inl p) =
    refl
  cases-is-section-map-inv-extension-equiv-complement-isolated-element y
    ( inl refl) (inr m) =
    ex-falso (m refl)
  cases-is-section-map-inv-extension-equiv-complement-isolated-element y
    ( inr n) (inl p) =
    ex-falso (pr2 (map-inv-equiv e (y , n)) p)
  cases-is-section-map-inv-extension-equiv-complement-isolated-element y
    ( inr n) (inr m) =
    ap
      ( pr1)
      ( ap
          ( λ t → map-equiv e (pr1 (map-inv-equiv e (y , n)) , t))
          ( eq-is-prop is-prop-neg) ∙
        is-section-map-inv-equiv e (y , n))

  is-section-map-inv-extension-equiv-complement-isolated-element :
    is-section
      map-extension-equiv-complement-isolated-element
      map-inv-extension-equiv-complement-isolated-element
  is-section-map-inv-extension-equiv-complement-isolated-element y =
    cases-is-section-map-inv-extension-equiv-complement-isolated-element y
      ( c y)
      ( d _)

  cases-is-retraction-map-inv-extension-equiv-complement-isolated-element :
    (x : A) (u : is-decidable (a ＝ x))
    (v :
      is-decidable
        ( b ＝ cases-map-extension-equiv-complement-isolated-element x u)) →
    cases-map-inv-extension-equiv-complement-isolated-element
      ( cases-map-extension-equiv-complement-isolated-element x u)
      ( v) ＝
    x
  cases-is-retraction-map-inv-extension-equiv-complement-isolated-element x
    ( inl p) (inl q) =
    p
  cases-is-retraction-map-inv-extension-equiv-complement-isolated-element x
    ( inl p) (inr n) =
    ex-falso (n refl)
  cases-is-retraction-map-inv-extension-equiv-complement-isolated-element x
    ( inr m) (inl q) =
    ex-falso (pr2 (map-equiv e (x , m)) q)
  cases-is-retraction-map-inv-extension-equiv-complement-isolated-element x
    ( inr m) (inr n) =
    ap pr1
      ( ap
          ( λ t → map-inv-equiv e (pr1 (map-equiv e (x , m)) , t))
          ( eq-is-prop is-prop-neg) ∙
        is-retraction-map-inv-equiv e (x , m))

  is-retraction-map-inv-extension-equiv-complement-isolated-element :
    is-retraction
      map-extension-equiv-complement-isolated-element
      map-inv-extension-equiv-complement-isolated-element
  is-retraction-map-inv-extension-equiv-complement-isolated-element x =
    cases-is-retraction-map-inv-extension-equiv-complement-isolated-element x
      ( d x)
      ( c _)

  is-equiv-extension-equiv-complement-isolated-element :
    is-equiv map-extension-equiv-complement-isolated-element
  is-equiv-extension-equiv-complement-isolated-element =
    is-equiv-is-invertible
      map-inv-extension-equiv-complement-isolated-element
      is-section-map-inv-extension-equiv-complement-isolated-element
      is-retraction-map-inv-extension-equiv-complement-isolated-element

  equiv-extension-equiv-complement-isolated-element : A ≃ B
  pr1 equiv-extension-equiv-complement-isolated-element =
    map-extension-equiv-complement-isolated-element
  pr2 equiv-extension-equiv-complement-isolated-element =
    is-equiv-extension-equiv-complement-isolated-element

  cases-preserves-point-extension-equiv-complement-isolated-element :
    (u : is-decidable (a ＝ a)) →
    cases-map-extension-equiv-complement-isolated-element a u ＝ b
  cases-preserves-point-extension-equiv-complement-isolated-element (inl p) =
    refl
  cases-preserves-point-extension-equiv-complement-isolated-element (inr n) =
    ex-falso (n refl)

  preserves-point-extension-equiv-complement-isolated-element :
    map-extension-equiv-complement-isolated-element a ＝ b
  preserves-point-extension-equiv-complement-isolated-element =
    cases-preserves-point-extension-equiv-complement-isolated-element (d a)

  extension-equiv-complement-isolated-element : (A , a) ≃∗ (B , b)
  pr1 extension-equiv-complement-isolated-element =
    equiv-extension-equiv-complement-isolated-element
  pr2 extension-equiv-complement-isolated-element =
    preserves-point-extension-equiv-complement-isolated-element
```

## Properties

### Equality of equivalences preserving isolated base points is characterized by homotopies

We show that equality of equivalences between types with isolated base points is
equivalent to [homotopies](foundation-core.homotopies.md) between them. Since
preserving the base point is a property, it is unnecessary to consider
[pointed homotopies](structured-types.pointed-homotopies.md).

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  ((a , d) : isolated-element A) ((b , c) : isolated-element B)
  where

  htpy-pointed-equiv-isolated-element :
    (e f : (A , a) ≃∗ (B , b)) → UU (l1 ⊔ l2)
  htpy-pointed-equiv-isolated-element e f =
    map-pointed-equiv e ~ map-pointed-equiv f

  refl-htpy-pointed-equiv-isolated-element :
    (e : (A , a) ≃∗ (B , b)) → htpy-pointed-equiv-isolated-element e e
  refl-htpy-pointed-equiv-isolated-element e =
    refl-htpy

  htpy-eq-pointed-equiv-isolated-element :
    (e f : (A , a) ≃∗ (B , b)) →
    e ＝ f → htpy-pointed-equiv-isolated-element e f
  htpy-eq-pointed-equiv-isolated-element e f refl =
    refl-htpy-pointed-equiv-isolated-element e

  is-torsorial-htpy-pointed-equiv-isolated-element :
    (e : (A , a) ≃∗ (B , b)) →
    is-torsorial (htpy-pointed-equiv-isolated-element e)
  is-torsorial-htpy-pointed-equiv-isolated-element (e , p) =
    is-torsorial-Eq-subtype
      ( is-torsorial-htpy-equiv e)
      ( λ f →
        is-prop-eq-isolated-element
          ( map-equiv f a)
          ( preserves-isolated-elements-equiv f d)
          ( b))
      ( e)
      ( refl-htpy)
      ( p)

  is-equiv-htpy-eq-pointed-equiv-isolated-element :
    (e f : (A , a) ≃∗ (B , b)) →
    is-equiv (htpy-eq-pointed-equiv-isolated-element e f)
  is-equiv-htpy-eq-pointed-equiv-isolated-element e =
    fundamental-theorem-id
      ( is-torsorial-htpy-pointed-equiv-isolated-element e)
      ( htpy-eq-pointed-equiv-isolated-element e)

  extensionality-pointed-equiv-isolated-element :
    (e f : (A , a) ≃∗ (B , b)) →
    (e ＝ f) ≃ htpy-pointed-equiv-isolated-element e f
  pr1 (extensionality-pointed-equiv-isolated-element e f) =
    htpy-eq-pointed-equiv-isolated-element e f
  pr2 (extensionality-pointed-equiv-isolated-element e f) =
    is-equiv-htpy-eq-pointed-equiv-isolated-element e f

  eq-htpy-pointed-equiv-isolated-element :
    (e f : (A , a) ≃∗ (B , b)) →
    htpy-pointed-equiv-isolated-element e f → e ＝ f
  eq-htpy-pointed-equiv-isolated-element e f =
    map-inv-equiv (extensionality-pointed-equiv-isolated-element e f)
```

### A pointed equivalence pointed at isolated elements is equivalently described by the induced equivalence on the complements

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  ((a , d) : isolated-element A) ((b , c) : isolated-element B)
  where

  map-compute-pointed-equiv-isolated-element :
    (A , a) ≃∗ (B , b) →
    complement-isolated-element (a , d) ≃ complement-isolated-element (b , c)
  map-compute-pointed-equiv-isolated-element =
    equiv-complement-isolated-element (a , d) (b , c)

  map-inv-compute-pointed-equiv-isolated-element :
    complement-isolated-element (a , d) ≃ complement-isolated-element (b , c) →
    (A , a) ≃∗ (B , b)
  map-inv-compute-pointed-equiv-isolated-element =
    extension-equiv-complement-isolated-element (a , d) (b , c)

  is-section-map-inv-compute-pointed-equiv-isolated-element :
    is-section
      map-compute-pointed-equiv-isolated-element
      map-inv-compute-pointed-equiv-isolated-element
  is-section-map-inv-compute-pointed-equiv-isolated-element e =
    eq-htpy-equiv
      ( λ (x , n) →
        eq-type-subtype
          ( is-in-complement-prop-isolated-element (b , c))
          ( compute-map-extension-equiv-complement-isolated-element
            ( a , d)
            ( b , c)
            ( e)
            ( x)
            ( n)))

  cases-is-retraction-map-inv-compute-pointed-equiv-isolated-element :
    (e : (A , a) ≃∗ (B , b)) (x : A) (u : is-decidable (a ＝ x)) →
    cases-map-extension-equiv-complement-isolated-element
      ( a , d)
      ( b , c)
      ( equiv-complement-isolated-element (a , d) (b , c) e)
      ( x)
      ( u) ＝
    map-pointed-equiv e x
  cases-is-retraction-map-inv-compute-pointed-equiv-isolated-element e x
    ( inl refl) =
    inv (preserves-point-pointed-equiv e)
  cases-is-retraction-map-inv-compute-pointed-equiv-isolated-element e x
    ( inr n) =
    refl

  is-retraction-map-inv-compute-pointed-equiv-isolated-element :
    is-retraction
      map-compute-pointed-equiv-isolated-element
      map-inv-compute-pointed-equiv-isolated-element
  is-retraction-map-inv-compute-pointed-equiv-isolated-element e =
    eq-htpy-pointed-equiv-isolated-element
      ( a , d)
      ( b , c)
      ( map-inv-compute-pointed-equiv-isolated-element
        ( map-compute-pointed-equiv-isolated-element e))
      ( e)
      ( λ x →
        cases-is-retraction-map-inv-compute-pointed-equiv-isolated-element e x
          ( d x))

  is-equiv-compute-pointed-equiv-isolated-element :
    is-equiv map-compute-pointed-equiv-isolated-element
  is-equiv-compute-pointed-equiv-isolated-element =
    is-equiv-is-invertible
      map-inv-compute-pointed-equiv-isolated-element
      is-section-map-inv-compute-pointed-equiv-isolated-element
      is-retraction-map-inv-compute-pointed-equiv-isolated-element

  compute-pointed-equiv-isolated-element :
    ( (A , a) ≃∗ (B , b)) ≃
    ( complement-isolated-element (a , d) ≃ complement-isolated-element (b , c))
  pr1 compute-pointed-equiv-isolated-element =
    map-compute-pointed-equiv-isolated-element
  pr2 compute-pointed-equiv-isolated-element =
    is-equiv-compute-pointed-equiv-isolated-element
```
