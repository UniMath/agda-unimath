# Surjective maps

```agda
module foundation.surjective-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.connected-maps
open import foundation.contractible-types
open import foundation.embeddings
open import foundation.homotopies
open import foundation.identity-types
open import foundation.monomorphisms
open import foundation.propositional-truncations
open import foundation.structure-identity-principle
open import foundation.truncated-types
open import foundation.type-theoretic-principle-of-choice
open import foundation.univalence
open import foundation.universal-property-propositional-truncation

open import foundation-core.constant-maps
open import foundation-core.contractible-maps
open import foundation-core.dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.functions
open import foundation-core.functoriality-dependent-function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.fundamental-theorem-of-identity-types
open import foundation-core.injective-maps
open import foundation-core.propositional-maps
open import foundation-core.propositions
open import foundation-core.sections
open import foundation-core.sets
open import foundation-core.subtype-identity-principle
open import foundation-core.truncated-maps
open import foundation-core.truncation-levels
open import foundation-core.universe-levels

open import orthogonal-factorization-systems.extensions-of-maps
```

</details>

## Idea

A map `f : A → B` is surjective if all of its fibers are inhabited.

## Definition

### Surjective maps

```agda
is-surjective-Prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → Prop (l1 ⊔ l2)
is-surjective-Prop {B = B} f =
  Π-Prop B (λ b → trunc-Prop (fib f b))

is-surjective :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
is-surjective f = type-Prop (is-surjective-Prop f)

is-prop-is-surjective :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-prop (is-surjective f)
is-prop-is-surjective f = is-prop-type-Prop (is-surjective-Prop f)

_↠_ :
  {l1 l2 : Level} → UU l1 → UU l2 → UU (l1 ⊔ l2)
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
Surjection l2 A = Σ (UU l2) (λ X → A ↠ X)

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
    sec f → is-surjective f
  is-surjective-has-section (pair g G) b = unit-trunc-Prop (pair (g b) (G b))
```

### Any equivalence is surjective

```agda
is-surjective-is-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-equiv f → is-surjective f
is-surjective-is-equiv H = is-surjective-has-section (pr1 H)

is-surjective-map-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
  is-surjective (map-equiv e)
is-surjective-map-equiv e = is-surjective-is-equiv (is-equiv-map-equiv e)
```

### The dependent universal property of surjective maps

```
dependent-universal-property-surj :
  (l : Level) {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  UU ((lsuc l) ⊔ l1 ⊔ l2)
dependent-universal-property-surj l {B = B} f =
  (P : B → Prop l) →
    is-equiv (λ (h : (b : B) → type-Prop (P b)) x → h (f x))

abstract
  is-surjective-dependent-universal-property-surj :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    ({l : Level} → dependent-universal-property-surj l f) →
    is-surjective f
  is-surjective-dependent-universal-property-surj f dup-surj-f =
    map-inv-is-equiv
      ( dup-surj-f (λ b → trunc-Prop (fib f b)))
      ( λ x → unit-trunc-Prop (pair x refl))

abstract
  square-dependent-universal-property-surj :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    (P : B → Prop l3) →
    ( λ (h : (y : B) → type-Prop (P y)) x → h (f x)) ~
    ( ( λ h x → h (f x) (pair x refl)) ∘
      ( ( λ h y → (h y) ∘ unit-trunc-Prop) ∘
        ( λ h y → const (type-trunc-Prop (fib f y)) (type-Prop (P y)) (h y))))
  square-dependent-universal-property-surj f P = refl-htpy

  dependent-universal-property-surj-is-surjective :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-surjective f →
    ({l : Level} → dependent-universal-property-surj l f)
  dependent-universal-property-surj-is-surjective f is-surj-f P =
    is-equiv-comp
      ( λ h x → h (f x) (pair x refl))
      ( ( λ h y → (h y) ∘ unit-trunc-Prop) ∘
        ( λ h y → const (type-trunc-Prop (fib f y)) (type-Prop (P y)) (h y)))
      ( is-equiv-comp
        ( λ h y → (h y) ∘ unit-trunc-Prop)
        ( λ h y → const (type-trunc-Prop (fib f y)) (type-Prop (P y)) (h y))
        ( is-equiv-map-Π
          ( λ y p z → p)
          ( λ y →
            is-equiv-diagonal-is-contr
              ( is-proof-irrelevant-is-prop
                ( is-prop-type-trunc-Prop)
                ( is-surj-f y))
              ( type-Prop (P y))))
        ( is-equiv-map-Π
          ( λ b g → g ∘ unit-trunc-Prop)
          ( λ b → is-propositional-truncation-trunc-Prop (fib f b) (P b))))
      ( is-equiv-map-reduce-Π-fib f ( λ y z → type-Prop (P y)))

equiv-dependent-universal-property-surj-is-surjective :
  {l l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-surjective f → (C : B → Prop l) →
  ((b : B) → type-Prop (C b)) ≃ ((a : A) → type-Prop (C (f a)))
pr1 (equiv-dependent-universal-property-surj-is-surjective f H C) h x = h (f x)
pr2 (equiv-dependent-universal-property-surj-is-surjective f H C) =
  dependent-universal-property-surj-is-surjective f H C

apply-dependent-universal-property-surj-is-surjective :
  {l l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-surjective f → (C : B → Prop l) →
  ((a : A) → type-Prop (C (f a))) → ((y : B) → type-Prop (C y))
apply-dependent-universal-property-surj-is-surjective f H C =
  map-inv-equiv (equiv-dependent-universal-property-surj-is-surjective f H C)
```

### A map into a proposition is a propositional truncation if and only if it is surjective

```agda
abstract
  is-surjective-is-propositional-truncation :
    {l1 l2 : Level} {A : UU l1} {P : Prop l2} (f : A → type-Prop P) →
    ( {l : Level} →
      dependent-universal-property-propositional-truncation l P f) →
    is-surjective f
  is-surjective-is-propositional-truncation f duppt-f =
    is-surjective-dependent-universal-property-surj f duppt-f

abstract
  is-propsitional-truncation-is-surjective :
    {l1 l2 : Level} {A : UU l1} {P : Prop l2} (f : A → type-Prop P) →
    is-surjective f →
    {l : Level} → dependent-universal-property-propositional-truncation l P f
  is-propsitional-truncation-is-surjective f is-surj-f =
    dependent-universal-property-surj-is-surjective f is-surj-f
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
            ( fib-emb-Prop (pair f K) y)
            ( id)))
```

### The composite of surjective maps is surjective

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  where

  abstract
    is-surjective-comp-htpy :
      (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
      is-surjective g → is-surjective h → is-surjective f
    is-surjective-comp-htpy f g h H is-surj-g is-surj-h x =
      apply-universal-property-trunc-Prop
        ( is-surj-g x)
        ( trunc-Prop (fib f x))
        ( λ { (pair b refl) →
          apply-universal-property-trunc-Prop
            ( is-surj-h b)
            ( trunc-Prop (fib f (g b)))
            ( λ { (pair a refl) →
              unit-trunc-Prop (pair a (H a))})})

  is-surjective-comp :
    {g : B → X} {h : A → B} →
    is-surjective g → is-surjective h → is-surjective (g ∘ h)
  is-surjective-comp {g} {h} =
    is-surjective-comp-htpy (g ∘ h) g h refl-htpy
```

### The composite of a surjective map with an equivalence is surjective

```agda
is-surjective-comp-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  (e : B ≃ C) → {f : A → B} → is-surjective f → is-surjective (map-equiv e ∘ f)
is-surjective-comp-equiv e =
  is-surjective-comp (is-surjective-map-equiv e)
```

### The precomposite of a surjective map with an equivalence is surjective

```agda
is-surjective-precomp-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {f : B → C} →
  is-surjective f → (e : A ≃ B) → is-surjective (f ∘ map-equiv e)
is-surjective-precomp-equiv H e =
  is-surjective-comp H (is-surjective-map-equiv e)
```

### If a composite is surjective, then so is its left factor

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  where

  abstract
    is-surjective-left-factor-htpy :
      (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
      is-surjective f → is-surjective g
    is-surjective-left-factor-htpy f g h H is-surj-f x =
      apply-universal-property-trunc-Prop
        ( is-surj-f x)
        ( trunc-Prop (fib g x))
        ( λ { (pair a refl) →
          unit-trunc-Prop (pair (h a) (inv (H a)))})

  is-surjective-left-factor :
    {g : B → X} (h : A → B) → is-surjective (g ∘ h) → is-surjective g
  is-surjective-left-factor {g} h =
    is-surjective-left-factor-htpy (g ∘ h) g h refl-htpy
```

### Surjective maps are -1-connected

```agda
is-neg-one-connected-map-is-surjective :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-surjective f → is-connected-map neg-one-𝕋 f
is-neg-one-connected-map-is-surjective H b =
  is-proof-irrelevant-is-prop is-prop-type-trunc-Prop (H b)
```

### Precomposing functions into a family of (k+1)-types by a surjective map is a k-truncated map

```agda
is-trunc-map-precomp-Π-is-surjective :
  {l1 l2 l3 : Level} (k : 𝕋) →
  {A : UU l1} {B : UU l2} {f : A → B} → is-surjective f →
  (P : B → Truncated-Type l3 (succ-𝕋 k)) →
  is-trunc-map k (precomp-Π f (λ b → type-Truncated-Type (P b)))
is-trunc-map-precomp-Π-is-surjective k H =
  is-trunc-map-precomp-Π-is-connected-map
    ( neg-one-𝕋)
    ( succ-𝕋 k)
    ( k)
    ( refl)
    ( is-neg-one-connected-map-is-surjective H)
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

  is-contr-total-htpy-surjection : is-contr (Σ (A ↠ B) htpy-surjection)
  is-contr-total-htpy-surjection =
    is-contr-total-Eq-subtype
      ( is-contr-total-htpy (map-surjection f))
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
    fundamental-theorem-id is-contr-total-htpy-surjection htpy-eq-surjection

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
    ( λ e → (map-equiv e ∘ map-Surjection f) ~ map-Surjection g)

module _
  {l1 l2 : Level} {A : UU l1} (f : Surjection l2 A)
  where

  id-equiv-Surjection : equiv-Surjection f f
  pr1 id-equiv-Surjection = id-equiv
  pr2 id-equiv-Surjection = refl-htpy

  is-contr-total-equiv-Surjection :
    is-contr (Σ (Surjection l2 A) (equiv-Surjection f))
  is-contr-total-equiv-Surjection =
    is-contr-total-Eq-structure
      ( λ Y g e → (map-equiv e ∘ map-Surjection f) ~ map-surjection g)
      ( is-contr-total-equiv (type-Surjection f))
      ( pair (type-Surjection f) id-equiv)
      ( is-contr-total-htpy-surjection (surjection-Surjection f))

  equiv-eq-Surjection :
    (g : Surjection l2 A) → (f ＝ g) → equiv-Surjection f g
  equiv-eq-Surjection .f refl = id-equiv-Surjection

  is-equiv-equiv-eq-Surjection :
    (g : Surjection l2 A) → is-equiv (equiv-eq-Surjection g)
  is-equiv-equiv-eq-Surjection =
    fundamental-theorem-id
      is-contr-total-equiv-Surjection
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

  is-surjective-postcomp-extension-surjective-map :
    (f : A → B) (i : A → X) (g : X → Y) →
    is-surjective f → is-emb g →
    is-surjective (postcomp-extension f i g)
  is-surjective-postcomp-extension-surjective-map f i g H K (h , L) =
    unit-trunc-Prop
      ( ( j , N) ,
        ( eq-htpy-extension f
          ( g ∘ i)
          ( postcomp-extension f i g (j , N))
          ( h , L)
          ( M)
          ( λ a →
            ( ap
              ( concat' (g (i a)) (M (f a)))
              ( issec-map-inv-is-equiv
                ( K (i a) ((j (f a))))
                ( L a ∙ inv (M (f a))))) ∙
            ( issec-inv-concat' (g (i a)) (M (f a)) (L a)))))
    where

    J : (b : B) → fib g (h b)
    J =
      apply-dependent-universal-property-surj-is-surjective f H
        ( λ b → fib-emb-Prop (g , K) (h b))
        ( λ a → (i a , L a))

    j : B → X
    j b = pr1 (J b)

    M : (g ∘ j) ~ h
    M b = pr2 (J b)

    N : i ~ (j ∘ f)
    N a = map-inv-is-equiv (K (i a) (j (f a))) (L a ∙ inv (M (f a)))

  is-equiv-postcomp-extension-is-surjective :
    (f : A → B) (i : A → X) (g : X → Y) →
    is-surjective f → is-emb g →
    is-equiv (postcomp-extension f i g)
  is-equiv-postcomp-extension-is-surjective f i g H K =
    is-equiv-is-emb-is-surjective
      ( is-surjective-postcomp-extension-surjective-map f i g H K)
      ( is-emb-postcomp-extension f i g K)

  equiv-postcomp-extension-surjection :
    (f : A ↠ B) (i : A → X) (g : X ↪ Y) →
    extension (map-surjection f) i ≃
    extension (map-surjection f) (map-emb g ∘ i)
  pr1 (equiv-postcomp-extension-surjection f i g) =
    postcomp-extension (map-surjection f) i (map-emb g)
  pr2 (equiv-postcomp-extension-surjection f i g) =
    is-equiv-postcomp-extension-is-surjective
      ( map-surjection f)
      ( i)
      ( map-emb g)
      ( is-surjective-map-surjection f)
      ( is-emb-map-emb g)
```
