# Surjective maps

```agda
module foundation.surjective-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.coinhabited-pairs-of-types
open import foundation.connected-maps
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.dependent-products-contractible-types
open import foundation.dependent-products-propositions
open import foundation.dependent-products-truncated-types
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equality-cartesian-product-types
open import foundation.equality-dependent-pair-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-propositional-truncation
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.postcomposition-dependent-functions
open import foundation.propositional-truncations
open import foundation.split-surjective-maps
open import foundation.structure-identity-principle
open import foundation.subtype-identity-principle
open import foundation.truncated-types
open import foundation.univalence
open import foundation.universal-property-family-of-fibers-of-maps
open import foundation.universal-property-propositional-truncation
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.constant-maps
open import foundation-core.contractible-maps
open import foundation-core.diagonal-maps-of-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-function-types
open import foundation-core.homotopies
open import foundation-core.precomposition-dependent-functions
open import foundation-core.propositional-maps
open import foundation-core.propositions
open import foundation-core.retracts-of-types
open import foundation-core.sections
open import foundation-core.sets
open import foundation-core.subtypes
open import foundation-core.torsorial-type-families
open import foundation-core.truncated-maps
open import foundation-core.truncation-levels

open import orthogonal-factorization-systems.equality-extensions-maps
open import orthogonal-factorization-systems.extensions-maps
open import orthogonal-factorization-systems.postcomposition-extensions-maps
```

</details>

## Idea

A map `f : A → B` is **surjective** if all of its
[fibers](foundation-core.fibers-of-maps.md) are
[inhabited](foundation.inhabited-types.md).

## Definition

### Surjective maps

```agda
is-surjective-Prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → Prop (l1 ⊔ l2)
is-surjective-Prop {B = B} f = Π-Prop B (trunc-Prop ∘ fiber f)

is-surjective :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
is-surjective f = type-Prop (is-surjective-Prop f)

is-prop-is-surjective :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-prop (is-surjective f)
is-prop-is-surjective f = is-prop-type-Prop (is-surjective-Prop f)

infix 5 _↠_
_↠_ : {l1 l2 : Level} → UU l1 → UU l2 → UU (l1 ⊔ l2)
A ↠ B = Σ (A → B) is-surjective

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A ↠ B)
  where

  map-surjection : A → B
  map-surjection = pr1 f

  is-surjective-map-surjection : is-surjective map-surjection
  is-surjective-map-surjection = pr2 f
```

### The type of all surjective maps out of a type

```agda
Surjection : {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
Surjection l2 A = Σ (UU l2) (A ↠_)

module _
  {l1 l2 : Level} {A : UU l1} (f : Surjection l2 A)
  where

  type-Surjection : UU l2
  type-Surjection = pr1 f

  surjection-Surjection : A ↠ type-Surjection
  surjection-Surjection = pr2 f

  map-Surjection : A → type-Surjection
  map-Surjection = map-surjection surjection-Surjection

  is-surjective-map-Surjection : is-surjective map-Surjection
  is-surjective-map-Surjection =
    is-surjective-map-surjection surjection-Surjection
```

### The type of all surjective maps into `k`-truncated types

```agda
Surjection-Into-Truncated-Type :
  {l1 : Level} (l2 : Level) (k : 𝕋) → UU l1 → UU (l1 ⊔ lsuc l2)
Surjection-Into-Truncated-Type l2 k A =
  Σ (Truncated-Type l2 k) (λ X → A ↠ type-Truncated-Type X)

emb-inclusion-Surjection-Into-Truncated-Type :
  {l1 : Level} (l2 : Level) (k : 𝕋) (A : UU l1) →
  Surjection-Into-Truncated-Type l2 k A ↪ Surjection l2 A
emb-inclusion-Surjection-Into-Truncated-Type l2 k A =
  emb-Σ (λ X → A ↠ X) (emb-type-Truncated-Type l2 k) (λ X → id-emb)

inclusion-Surjection-Into-Truncated-Type :
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} →
  Surjection-Into-Truncated-Type l2 k A → Surjection l2 A
inclusion-Surjection-Into-Truncated-Type {l1} {l2} {k} {A} =
  map-emb (emb-inclusion-Surjection-Into-Truncated-Type l2 k A)

module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1}
  (f : Surjection-Into-Truncated-Type l2 k A)
  where

  truncated-type-Surjection-Into-Truncated-Type : Truncated-Type l2 k
  truncated-type-Surjection-Into-Truncated-Type = pr1 f

  type-Surjection-Into-Truncated-Type : UU l2
  type-Surjection-Into-Truncated-Type =
    type-Truncated-Type truncated-type-Surjection-Into-Truncated-Type

  is-trunc-type-Surjection-Into-Truncated-Type :
    is-trunc k type-Surjection-Into-Truncated-Type
  is-trunc-type-Surjection-Into-Truncated-Type =
    is-trunc-type-Truncated-Type
      truncated-type-Surjection-Into-Truncated-Type

  surjection-Surjection-Into-Truncated-Type :
    A ↠ type-Surjection-Into-Truncated-Type
  surjection-Surjection-Into-Truncated-Type = pr2 f

  map-Surjection-Into-Truncated-Type :
    A → type-Surjection-Into-Truncated-Type
  map-Surjection-Into-Truncated-Type =
    map-surjection surjection-Surjection-Into-Truncated-Type

  is-surjective-Surjection-Into-Truncated-Type :
    is-surjective map-Surjection-Into-Truncated-Type
  is-surjective-Surjection-Into-Truncated-Type =
    is-surjective-map-surjection surjection-Surjection-Into-Truncated-Type
```

### The type of all surjective maps into sets

```agda
Surjection-Into-Set :
  {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
Surjection-Into-Set l2 A = Surjection-Into-Truncated-Type l2 zero-𝕋 A

emb-inclusion-Surjection-Into-Set :
  {l1 : Level} (l2 : Level) (A : UU l1) →
  Surjection-Into-Set l2 A ↪ Surjection l2 A
emb-inclusion-Surjection-Into-Set l2 A =
  emb-inclusion-Surjection-Into-Truncated-Type l2 zero-𝕋 A

inclusion-Surjection-Into-Set :
  {l1 l2 : Level} {A : UU l1} →
  Surjection-Into-Set l2 A → Surjection l2 A
inclusion-Surjection-Into-Set {l1} {l2} {A} =
  inclusion-Surjection-Into-Truncated-Type

module _
  {l1 l2 : Level} {A : UU l1} (f : Surjection-Into-Set l2 A)
  where

  set-Surjection-Into-Set : Set l2
  set-Surjection-Into-Set = truncated-type-Surjection-Into-Truncated-Type f

  type-Surjection-Into-Set : UU l2
  type-Surjection-Into-Set = type-Surjection-Into-Truncated-Type f

  is-set-type-Surjection-Into-Set : is-set type-Surjection-Into-Set
  is-set-type-Surjection-Into-Set =
    is-trunc-type-Surjection-Into-Truncated-Type f

  surjection-Surjection-Into-Set : A ↠ type-Surjection-Into-Set
  surjection-Surjection-Into-Set = surjection-Surjection-Into-Truncated-Type f

  map-Surjection-Into-Set : A → type-Surjection-Into-Set
  map-Surjection-Into-Set = map-Surjection-Into-Truncated-Type f

  is-surjective-Surjection-Into-Set : is-surjective map-Surjection-Into-Set
  is-surjective-Surjection-Into-Set =
    is-surjective-Surjection-Into-Truncated-Type f
```

## Properties

### Any map that has a section is surjective

```agda
abstract
  is-surjective-has-section :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
    section f → is-surjective f
  is-surjective-has-section (g , G) b = unit-trunc-Prop (g b , G b)
```

### The underlying surjection of a retract

```agda
surjection-retract :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  A retract-of B → B ↠ A
surjection-retract R =
  ( map-retraction-retract R , is-surjective-has-section (section-retract R))
```

### If an empty type has a surjection into another type, that type is empty

```agda
abstract
  is-empty-surjection :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} → A ↠ B → is-empty A → is-empty B
  is-empty-surjection A↠B ¬A b =
    rec-trunc-Prop empty-Prop (¬A ∘ pr1) (is-surjective-map-surjection A↠B b)
```

### If a type `A` has a surjection into `B`, `A` and `B` are coinhabited

```agda
abstract
  is-coinhabited-surjection :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} → A ↠ B → is-coinhabited A B
  pr1 (is-coinhabited-surjection A↠B) = map-is-inhabited (map-surjection A↠B)
  pr2 (is-coinhabited-surjection A↠B) |B| =
    let open do-syntax-trunc-Prop (is-inhabited-Prop _)
    in do
      b ← |B|
      (a , fa=b) ← is-surjective-map-surjection A↠B b
      unit-trunc-Prop a
```

### Any split surjective map is surjective

```agda
abstract
  is-surjective-is-split-surjective :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
    is-split-surjective f → is-surjective f
  is-surjective-is-split-surjective H x =
    unit-trunc-Prop (H x)
```

### Any equivalence is surjective

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-surjective-is-equiv : {f : A → B} → is-equiv f → is-surjective f
  is-surjective-is-equiv H = is-surjective-has-section (pr1 H)

  is-surjective-map-equiv : (e : A ≃ B) → is-surjective (map-equiv e)
  is-surjective-map-equiv e = is-surjective-is-equiv (is-equiv-map-equiv e)

  surjection-equiv : A ≃ B → A ↠ B
  surjection-equiv e = map-equiv e , is-surjective-map-equiv e

  surjection-inv-equiv : B ≃ A → A ↠ B
  surjection-inv-equiv e = surjection-equiv (inv-equiv e)
```

### The identity function is surjective

```agda
module _
  {l : Level} {A : UU l}
  where

  is-surjective-id : is-surjective (id {A = A})
  is-surjective-id a = unit-trunc-Prop (a , refl)

  id-surjection : A ↠ A
  id-surjection = (id , is-surjective-id)
```

### Maps which are homotopic to surjective maps are surjective

```agda
module _
  { l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-surjective-htpy :
      {f g : A → B} → f ~ g → is-surjective g → is-surjective f
    is-surjective-htpy {f} {g} H K b =
      apply-universal-property-trunc-Prop
        ( K b)
        ( trunc-Prop (fiber f b))
        ( λ where (a , refl) → unit-trunc-Prop (a , H a))

  abstract
    is-surjective-htpy' :
      {f g : A → B} → f ~ g → is-surjective f → is-surjective g
    is-surjective-htpy' H = is-surjective-htpy (inv-htpy H)
```

### The dependent universal property of surjective maps

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  dependent-universal-property-surjection : UUω
  dependent-universal-property-surjection =
    {l : Level} (P : B → Prop l) →
    is-equiv (λ (h : (b : B) → type-Prop (P b)) x → h (f x))

  abstract
    is-surjective-dependent-universal-property-surjection :
      dependent-universal-property-surjection → is-surjective f
    is-surjective-dependent-universal-property-surjection dup-surj-f =
      map-inv-is-equiv
        ( dup-surj-f (λ b → trunc-Prop (fiber f b)))
        ( λ x → unit-trunc-Prop (x , refl))

  abstract
    square-dependent-universal-property-surjection :
      {l3 : Level} (P : B → Prop l3) →
      ( λ (h : (y : B) → type-Prop (P y)) x → h (f x)) ~
      ( ( λ h x → h (f x) (x , refl)) ∘
        ( λ h y → h y ∘ unit-trunc-Prop) ∘
        ( postcomp-Π _
          ( λ {y} →
            diagonal-exponential
              ( type-Prop (P y))
              ( type-trunc-Prop (fiber f y)))))
    square-dependent-universal-property-surjection P = refl-htpy

  abstract
    dependent-universal-property-surjection-is-surjective :
      is-surjective f → dependent-universal-property-surjection
    dependent-universal-property-surjection-is-surjective is-surj-f P =
      is-equiv-comp
        ( λ h x → h (f x) (x , refl))
        ( ( λ h y → h y ∘ unit-trunc-Prop) ∘
          ( postcomp-Π
            ( B)
            ( λ {y} →
              diagonal-exponential
                ( type-Prop (P y))
                ( type-trunc-Prop (fiber f y)))))
        ( is-equiv-comp
          ( λ h y → h y ∘ unit-trunc-Prop)
          ( postcomp-Π
            ( B)
            ( λ {y} →
              diagonal-exponential
                ( type-Prop (P y))
                ( type-trunc-Prop (fiber f y))))
          ( is-equiv-map-Π-is-fiberwise-equiv
            ( λ y →
              is-equiv-diagonal-exponential-is-contr
                ( is-proof-irrelevant-is-prop
                  ( is-prop-type-trunc-Prop)
                  ( is-surj-f y))
                ( type-Prop (P y))))
          ( is-equiv-map-Π-is-fiberwise-equiv
            ( λ b → is-propositional-truncation-trunc-Prop (fiber f b) (P b))))
        ( universal-property-family-of-fibers-fiber f (is-in-subtype P))

  equiv-dependent-universal-property-surjection-is-surjective :
    is-surjective f →
    {l : Level} (C : B → Prop l) →
    ((b : B) → type-Prop (C b)) ≃ ((a : A) → type-Prop (C (f a)))
  pr1 (equiv-dependent-universal-property-surjection-is-surjective H C) h x =
    h (f x)
  pr2 (equiv-dependent-universal-property-surjection-is-surjective H C) =
    dependent-universal-property-surjection-is-surjective H C

  apply-dependent-universal-property-surjection-is-surjective :
    is-surjective f →
    {l : Level} (C : B → Prop l) →
    ((a : A) → type-Prop (C (f a))) → ((y : B) → type-Prop (C y))
  apply-dependent-universal-property-surjection-is-surjective H C =
    map-inv-equiv
      ( equiv-dependent-universal-property-surjection-is-surjective H C)

  apply-twice-dependent-universal-property-surjection-is-surjective :
    is-surjective f →
    {l : Level} (C : B → B → Prop l) →
    ((x y : A) → type-Prop (C (f x) (f y))) → ((s t : B) → type-Prop (C s t))
  apply-twice-dependent-universal-property-surjection-is-surjective H C G s =
    apply-dependent-universal-property-surjection-is-surjective
      ( H)
      ( λ b → C s b)
      ( λ y →
        apply-dependent-universal-property-surjection-is-surjective
          ( H)
          ( λ b → C b (f y))
          ( λ x → G x y)
          ( s))

equiv-dependent-universal-property-surjection :
  {l l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A ↠ B) →
  (C : B → Prop l) →
  ((b : B) → type-Prop (C b)) ≃ ((a : A) → type-Prop (C (map-surjection f a)))
equiv-dependent-universal-property-surjection f =
  equiv-dependent-universal-property-surjection-is-surjective
    ( map-surjection f)
    ( is-surjective-map-surjection f)

apply-dependent-universal-property-surjection :
  {l l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A ↠ B) →
  (C : B → Prop l) →
  ((a : A) → type-Prop (C (map-surjection f a))) → ((y : B) → type-Prop (C y))
apply-dependent-universal-property-surjection f =
  apply-dependent-universal-property-surjection-is-surjective
    ( map-surjection f)
    ( is-surjective-map-surjection f)
```

### A map into a proposition is a propositional truncation if and only if it is surjective

```agda
abstract
  is-surjective-is-propositional-truncation :
    {l1 l2 : Level} {A : UU l1} {P : Prop l2} (f : A → type-Prop P) →
    dependent-universal-property-propositional-truncation P f →
    is-surjective f
  is-surjective-is-propositional-truncation f duppt-f =
    is-surjective-dependent-universal-property-surjection f duppt-f

abstract
  is-propositional-truncation-is-surjective :
    {l1 l2 : Level} {A : UU l1} {P : Prop l2} (f : A → type-Prop P) →
    is-surjective f →
    dependent-universal-property-propositional-truncation P f
  is-propositional-truncation-is-surjective f is-surj-f =
    dependent-universal-property-surjection-is-surjective f is-surj-f

abstract
  is-surjective-unit-trunc-Prop :
    {l : Level} (A : UU l) → is-surjective (unit-trunc-Prop {A = A})
  is-surjective-unit-trunc-Prop A =
    is-surjective-is-propositional-truncation
      { P = trunc-Prop A}
      ( unit-trunc-Prop)
      ( dependent-universal-property-trunc-Prop)

surjection-unit-trunc-Prop :
  {l : Level} (A : UU l) → A ↠ type-trunc-Prop A
surjection-unit-trunc-Prop A =
  ( unit-trunc-Prop , is-surjective-unit-trunc-Prop A)
```

### A map that is both surjective and an embedding is an equivalence

```agda
abstract
  is-equiv-is-emb-is-surjective :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
    is-surjective f → is-emb f → is-equiv f
  is-equiv-is-emb-is-surjective {f = f} H K =
    is-equiv-is-contr-map
      ( λ y →
        is-proof-irrelevant-is-prop
          ( is-prop-map-is-emb K y)
          ( apply-universal-property-trunc-Prop
            ( H y)
            ( fiber-emb-Prop (f , K) y)
            ( id)))
```

### The composite of surjective maps is surjective

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  where

  abstract
    is-surjective-left-map-triangle :
      (f : A → X) (g : B → X) (h : A → B) (H : f ~ g ∘ h) →
      is-surjective g → is-surjective h → is-surjective f
    is-surjective-left-map-triangle f g h H is-surj-g is-surj-h x =
      apply-universal-property-trunc-Prop
        ( is-surj-g x)
        ( trunc-Prop (fiber f x))
        ( λ where
          ( b , refl) →
            apply-universal-property-trunc-Prop
              ( is-surj-h b)
              ( trunc-Prop (fiber f (g b)))
              ( λ where (a , refl) → unit-trunc-Prop (a , H a)))

  is-surjective-comp :
    {g : B → X} {h : A → B} →
    is-surjective g → is-surjective h → is-surjective (g ∘ h)
  is-surjective-comp {g} {h} =
    is-surjective-left-map-triangle (g ∘ h) g h refl-htpy

  comp-surjection : B ↠ X → A ↠ B → A ↠ X
  comp-surjection (g , G) (h , H) = g ∘ h , is-surjective-comp G H
```

### Functoriality of products preserves being surjective

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  where

  abstract
    is-surjective-map-product :
      {f : A → C} {g : B → D} →
      is-surjective f → is-surjective g → is-surjective (map-product f g)
    is-surjective-map-product {f} {g} s s' (c , d) =
      apply-twice-universal-property-trunc-Prop
        ( s c)
        ( s' d)
        ( trunc-Prop (fiber (map-product f g) (c , d)))
        ( λ x y →
          unit-trunc-Prop ((pr1 x , pr1 y) , eq-pair (pr2 x) (pr2 y)))

  surjection-product :
    (A ↠ C) → (B ↠ D) → ((A × B) ↠ (C × D))
  pr1 (surjection-product f g) =
    map-product (map-surjection f) (map-surjection g)
  pr2 (surjection-product f g) =
    is-surjective-map-product
      ( is-surjective-map-surjection f)
      ( is-surjective-map-surjection g)
```

### Functoriality of coproducts preserves being surjective

```agda
module _
  {l1 l2 l1' l2' : Level} {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
  where

  abstract
    is-surjective-map-coproduct :
      {f : A → A'} {g : B → B'} →
      is-surjective f → is-surjective g →
      is-surjective (map-coproduct f g)
    is-surjective-map-coproduct s s' (inl x) =
      apply-universal-property-trunc-Prop (s x)
        ( trunc-Prop (fiber (map-coproduct _ _) (inl x)))
        ( λ (a , p) → unit-trunc-Prop (inl a , ap inl p))
    is-surjective-map-coproduct s s' (inr x) =
      apply-universal-property-trunc-Prop (s' x)
        ( trunc-Prop (fiber (map-coproduct _ _) (inr x)))
        ( λ (a , p) → unit-trunc-Prop (inr a , ap inr p))

  surjection-coproduct :
    (A ↠ A') → (B ↠ B') → ((A + B) ↠ (A' + B'))
  surjection-coproduct (f , sf) (g , sg) =
    ( map-coproduct f g ,
      is-surjective-map-coproduct sf sg)
```

### Surjectivity of maps on total spaces

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  where

  abstract
    is-surjective-tot :
      (f : (a : A) → B a → C a) →
      ((a : A) → is-surjective (f a)) → is-surjective (tot f)
    is-surjective-tot f H (a , c) =
      map-trunc-Prop
        ( λ (b , fab=c) → ((a , b) , eq-pair-eq-fiber fab=c))
        ( H a c)

  surjection-tot : ((a : A) → B a ↠ C a) → Σ A B ↠ Σ A C
  surjection-tot f =
    ( tot (λ a → map-surjection (f a)) ,
      is-surjective-tot _ (λ a → is-surjective-map-surjection (f a)))
```

### The composite of a surjective map before an equivalence is surjective

```agda
is-surjective-left-comp-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  (e : B ≃ C) {f : A → B} → is-surjective f → is-surjective (map-equiv e ∘ f)
is-surjective-left-comp-equiv e =
  is-surjective-comp (is-surjective-map-equiv e)
```

### The composite of a surjective map after an equivalence is surjective

```agda
is-surjective-right-comp-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {f : B → C} →
  is-surjective f → (e : A ≃ B) → is-surjective (f ∘ map-equiv e)
is-surjective-right-comp-equiv H e =
  is-surjective-comp H (is-surjective-map-equiv e)
```

### If a composite is surjective, then so is its left factor

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  where

  abstract
    is-surjective-right-map-triangle :
      (f : A → X) (g : B → X) (h : A → B) (H : f ~ g ∘ h) →
      is-surjective f → is-surjective g
    is-surjective-right-map-triangle f g h H is-surj-f x =
      apply-universal-property-trunc-Prop
        ( is-surj-f x)
        ( trunc-Prop (fiber g x))
        ( λ where (a , refl) → unit-trunc-Prop (h a , inv (H a)))

  is-surjective-left-factor :
    {g : B → X} (h : A → B) → is-surjective (g ∘ h) → is-surjective g
  is-surjective-left-factor {g} h =
    is-surjective-right-map-triangle (g ∘ h) g h refl-htpy
```

### Surjective maps are `-1`-connected

```agda
is-neg-one-connected-map-is-surjective :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-surjective f → is-connected-map neg-one-𝕋 f
is-neg-one-connected-map-is-surjective H b =
  is-proof-irrelevant-is-prop is-prop-type-trunc-Prop (H b)

is-surjective-is-neg-one-connected-map :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-connected-map neg-one-𝕋 f → is-surjective f
is-surjective-is-neg-one-connected-map H b = center (H b)
```

### A (k+1)-connected map is surjective

```agda
is-surjective-is-connected-map :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2}
  {f : A → B} → is-connected-map (succ-𝕋 k) f →
  is-surjective f
is-surjective-is-connected-map neg-two-𝕋 H =
  is-surjective-is-neg-one-connected-map H
is-surjective-is-connected-map (succ-𝕋 k) H =
  is-surjective-is-connected-map
    ( k)
    ( is-connected-map-is-connected-map-succ-𝕋
      ( succ-𝕋 k)
      ( H))
```

### Precomposing functions into a family of `k+1`-types by a surjective map is a `k`-truncated map

```agda
is-trunc-map-precomp-Π-is-surjective :
  {l1 l2 l3 : Level} (k : 𝕋) →
  {A : UU l1} {B : UU l2} {f : A → B} → is-surjective f →
  (P : B → Truncated-Type l3 (succ-𝕋 k)) →
  is-trunc-map k (precomp-Π f (λ b → type-Truncated-Type (P b)))
is-trunc-map-precomp-Π-is-surjective k H =
  is-trunc-map-precomp-Π-is-connected-map'
    ( neg-one-𝕋)
    ( k)
    ( is-neg-one-connected-map-is-surjective H)
```

### Precomposing functions into a family of propositions by a surjective map is an equivalence

```agda
module _
  {l1 l2 l3 : Level}
  {A : UU l1} {B : UU l2} {f : A → B}
  (H : is-surjective f)
  where

  is-equiv-precomp-Π-Prop-is-surjective :
    (P : B → Prop l3) →
    is-equiv (precomp-Π f (type-Prop ∘ P))
  is-equiv-precomp-Π-Prop-is-surjective P =
    is-equiv-is-contr-map (is-trunc-map-precomp-Π-is-surjective neg-two-𝕋 H P)

  map-inv-is-equiv-precomp-Π-Prop-is-surjective :
    (P : B → Prop l3) →
    ((a : A) → type-Prop (P (f a))) → (b : B) → type-Prop (P b)
  map-inv-is-equiv-precomp-Π-Prop-is-surjective P =
    map-inv-is-equiv (is-equiv-precomp-Π-Prop-is-surjective P)
```

### Characterization of the identity type of `A ↠ B`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A ↠ B)
  where

  htpy-surjection : (A ↠ B) → UU (l1 ⊔ l2)
  htpy-surjection g = map-surjection f ~ map-surjection g

  refl-htpy-surjection : htpy-surjection f
  refl-htpy-surjection = refl-htpy

  is-torsorial-htpy-surjection : is-torsorial htpy-surjection
  is-torsorial-htpy-surjection =
    is-torsorial-Eq-subtype
      ( is-torsorial-htpy (map-surjection f))
      ( is-prop-is-surjective)
      ( map-surjection f)
      ( refl-htpy)
      ( is-surjective-map-surjection f)

  htpy-eq-surjection :
    (g : A ↠ B) → (f ＝ g) → htpy-surjection g
  htpy-eq-surjection .f refl = refl-htpy-surjection

  is-equiv-htpy-eq-surjection :
    (g : A ↠ B) → is-equiv (htpy-eq-surjection g)
  is-equiv-htpy-eq-surjection =
    fundamental-theorem-id is-torsorial-htpy-surjection htpy-eq-surjection

  extensionality-surjection :
    (g : A ↠ B) → (f ＝ g) ≃ htpy-surjection g
  pr1 (extensionality-surjection g) = htpy-eq-surjection g
  pr2 (extensionality-surjection g) = is-equiv-htpy-eq-surjection g

  eq-htpy-surjection : (g : A ↠ B) → htpy-surjection g → f ＝ g
  eq-htpy-surjection g =
    map-inv-equiv (extensionality-surjection g)
```

### Characterization of the identity type of `Surjection l2 A`

```agda
equiv-Surjection :
  {l1 l2 l3 : Level} {A : UU l1} →
  Surjection l2 A → Surjection l3 A → UU (l1 ⊔ l2 ⊔ l3)
equiv-Surjection f g =
  Σ ( type-Surjection f ≃ type-Surjection g)
    ( λ e → map-equiv e ∘ map-Surjection f ~ map-Surjection g)

module _
  {l1 l2 : Level} {A : UU l1} (f : Surjection l2 A)
  where

  id-equiv-Surjection : equiv-Surjection f f
  pr1 id-equiv-Surjection = id-equiv
  pr2 id-equiv-Surjection = refl-htpy

  is-torsorial-equiv-Surjection :
    is-torsorial (equiv-Surjection f)
  is-torsorial-equiv-Surjection =
    is-torsorial-Eq-structure
      ( is-torsorial-equiv (type-Surjection f))
      ( type-Surjection f , id-equiv)
      ( is-torsorial-htpy-surjection (surjection-Surjection f))

  equiv-eq-Surjection :
    (g : Surjection l2 A) → (f ＝ g) → equiv-Surjection f g
  equiv-eq-Surjection .f refl = id-equiv-Surjection

  is-equiv-equiv-eq-Surjection :
    (g : Surjection l2 A) → is-equiv (equiv-eq-Surjection g)
  is-equiv-equiv-eq-Surjection =
    fundamental-theorem-id
      is-torsorial-equiv-Surjection
      equiv-eq-Surjection

  extensionality-Surjection :
    (g : Surjection l2 A) → (f ＝ g) ≃ equiv-Surjection f g
  pr1 (extensionality-Surjection g) = equiv-eq-Surjection g
  pr2 (extensionality-Surjection g) = is-equiv-equiv-eq-Surjection g

  eq-equiv-Surjection :
    (g : Surjection l2 A) → equiv-Surjection f g → f ＝ g
  eq-equiv-Surjection g = map-inv-equiv (extensionality-Surjection g)
```

### Characterization of the identity type of `Surjection-Into-Truncated-Type l2 k A`

```agda
equiv-Surjection-Into-Truncated-Type :
  {l1 l2 l3 : Level} {k : 𝕋} {A : UU l1} →
  Surjection-Into-Truncated-Type l2 k A →
  Surjection-Into-Truncated-Type l3 k A → UU (l1 ⊔ l2 ⊔ l3)
equiv-Surjection-Into-Truncated-Type f g =
  equiv-Surjection
    ( inclusion-Surjection-Into-Truncated-Type f)
    ( inclusion-Surjection-Into-Truncated-Type g)

module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1}
  (f : Surjection-Into-Truncated-Type l2 k A)
  where

  id-equiv-Surjection-Into-Truncated-Type :
    equiv-Surjection-Into-Truncated-Type f f
  id-equiv-Surjection-Into-Truncated-Type =
    id-equiv-Surjection (inclusion-Surjection-Into-Truncated-Type f)

  extensionality-Surjection-Into-Truncated-Type :
    (g : Surjection-Into-Truncated-Type l2 k A) →
    (f ＝ g) ≃ equiv-Surjection-Into-Truncated-Type f g
  extensionality-Surjection-Into-Truncated-Type g =
    ( extensionality-Surjection
      ( inclusion-Surjection-Into-Truncated-Type f)
      ( inclusion-Surjection-Into-Truncated-Type g)) ∘e
    ( equiv-ap-emb (emb-inclusion-Surjection-Into-Truncated-Type l2 k A))

  equiv-eq-Surjection-Into-Truncated-Type :
    (g : Surjection-Into-Truncated-Type l2 k A) →
    (f ＝ g) → equiv-Surjection-Into-Truncated-Type f g
  equiv-eq-Surjection-Into-Truncated-Type g =
    map-equiv (extensionality-Surjection-Into-Truncated-Type g)

  refl-equiv-eq-Surjection-Into-Truncated-Type :
    equiv-eq-Surjection-Into-Truncated-Type f refl ＝
    id-equiv-Surjection-Into-Truncated-Type
  refl-equiv-eq-Surjection-Into-Truncated-Type = refl

  eq-equiv-Surjection-Into-Truncated-Type :
    (g : Surjection-Into-Truncated-Type l2 k A) →
    equiv-Surjection-Into-Truncated-Type f g → f ＝ g
  eq-equiv-Surjection-Into-Truncated-Type g =
    map-inv-equiv (extensionality-Surjection-Into-Truncated-Type g)
```

### The type `Surjection-Into-Truncated-Type l2 (succ-𝕋 k) A` is `k`-truncated

This remains to be shown.
[#735](https://github.com/UniMath/agda-unimath/issues/735)

### Characterization of the identity type of `Surjection-Into-Set l2 A`

```agda
equiv-Surjection-Into-Set :
  {l1 l2 l3 : Level} {A : UU l1} → Surjection-Into-Set l2 A →
  Surjection-Into-Set l3 A → UU (l1 ⊔ l2 ⊔ l3)
equiv-Surjection-Into-Set = equiv-Surjection-Into-Truncated-Type

id-equiv-Surjection-Into-Set :
  {l1 l2 : Level} {A : UU l1} (f : Surjection-Into-Set l2 A) →
  equiv-Surjection-Into-Set f f
id-equiv-Surjection-Into-Set = id-equiv-Surjection-Into-Truncated-Type

extensionality-Surjection-Into-Set :
  {l1 l2 : Level} {A : UU l1} (f g : Surjection-Into-Set l2 A) →
  (f ＝ g) ≃ equiv-Surjection-Into-Set f g
extensionality-Surjection-Into-Set =
  extensionality-Surjection-Into-Truncated-Type

equiv-eq-Surjection-Into-Set :
  {l1 l2 : Level} {A : UU l1} (f g : Surjection-Into-Set l2 A) →
  (f ＝ g) → equiv-Surjection-Into-Set f g
equiv-eq-Surjection-Into-Set = equiv-eq-Surjection-Into-Truncated-Type

refl-equiv-eq-Surjection-Into-Set :
  {l1 l2 : Level} {A : UU l1} (f : Surjection-Into-Set l2 A) →
  equiv-eq-Surjection-Into-Set f f refl ＝
  id-equiv-Surjection-Into-Set f
refl-equiv-eq-Surjection-Into-Set = refl-equiv-eq-Surjection-Into-Truncated-Type

eq-equiv-Surjection-Into-Set :
  {l1 l2 : Level} {A : UU l1} (f g : Surjection-Into-Set l2 A) →
  equiv-Surjection-Into-Set f g → f ＝ g
eq-equiv-Surjection-Into-Set = eq-equiv-Surjection-Into-Truncated-Type
```

### Postcomposition of extensions along surjective maps by an embedding is an equivalence

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  where

  is-surjective-postcomp-extension-map-surjective-map :
    (f : A → B) (i : A → X) (g : X → Y) →
    is-surjective f → is-emb g →
    is-surjective (postcomp-extension-map f i g)
  is-surjective-postcomp-extension-map-surjective-map f i g H K (h , L) =
    unit-trunc-Prop
      ( ( j , N) ,
        ( eq-htpy-extension-map f
          ( g ∘ i)
          ( postcomp-extension-map f i g (j , N))
          ( h , L)
          ( M ,
            λ a →
            ( ap
              ( concat' (g (i a)) (M (f a)))
              ( is-section-map-inv-is-equiv
                ( K (i a) (j (f a)))
                ( L a ∙ inv (M (f a))))) ∙
            ( is-section-inv-concat' (M (f a)) (L a)))))
    where

    J : (b : B) → fiber g (h b)
    J =
      apply-dependent-universal-property-surjection-is-surjective f H
        ( λ b → fiber-emb-Prop (g , K) (h b))
        ( λ a → (i a , L a))

    j : B → X
    j b = pr1 (J b)

    M : (g ∘ j) ~ h
    M b = pr2 (J b)

    N : i ~ (j ∘ f)
    N a = map-inv-is-equiv (K (i a) (j (f a))) (L a ∙ inv (M (f a)))

  is-equiv-postcomp-extension-map-is-surjective :
    (f : A → B) (i : A → X) (g : X → Y) →
    is-surjective f → is-emb g →
    is-equiv (postcomp-extension-map f i g)
  is-equiv-postcomp-extension-map-is-surjective f i g H K =
    is-equiv-is-emb-is-surjective
      ( is-surjective-postcomp-extension-map-surjective-map f i g H K)
      ( is-emb-postcomp-extension-map f i g K)

  equiv-postcomp-extension-map-surjection :
    (f : A ↠ B) (i : A → X) (g : X ↪ Y) →
    extension-map (map-surjection f) i ≃
    extension-map (map-surjection f) (map-emb g ∘ i)
  pr1 (equiv-postcomp-extension-map-surjection f i g) =
    postcomp-extension-map (map-surjection f) i (map-emb g)
  pr2 (equiv-postcomp-extension-map-surjection f i g) =
    is-equiv-postcomp-extension-map-is-surjective
      ( map-surjection f)
      ( i)
      ( map-emb g)
      ( is-surjective-map-surjection f)
      ( is-emb-map-emb g)
```

### Every type that surjects onto an inhabited type is inhabited

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-inhabited-is-surjective :
    {f : A → B} → is-surjective f → is-inhabited B → is-inhabited A
  is-inhabited-is-surjective F =
    rec-trunc-Prop (is-inhabited-Prop A) (map-trunc-Prop pr1 ∘ F)

  is-inhabited-surjection :
    A ↠ B → is-inhabited B → is-inhabited A
  is-inhabited-surjection f =
    is-inhabited-is-surjective (is-surjective-map-surjection f)
```

### The type of surjections `A ↠ B` is equivalent to the type of families `P` of inhabited types over `B` equipped with an equivalence `A ≃ Σ B P`

> This remains to be shown.
> [#735](https://github.com/UniMath/agda-unimath/issues/735)

## See also

- In
  [Epimorphisms with respect to sets](foundation.epimorphisms-with-respect-to-sets.md)
  we show that a map is surjective if and only if it is an epimorphism with
  respect to sets.
