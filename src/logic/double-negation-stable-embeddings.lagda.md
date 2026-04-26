# Double negation stable embeddings

```agda
module logic.double-negation-stable-embeddings where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-morphisms-arrows
open import foundation.decidable-embeddings
open import foundation.dependent-pair-types
open import foundation.double-negation-stable-propositions
open import foundation.embeddings
open import foundation.fibers-of-maps
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-coproduct-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositional-maps
open import foundation.propositions
open import foundation.retracts-of-arrows
open import foundation.subtype-identity-principle
open import foundation.unit-type
open import foundation.universal-property-equivalences
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.injective-maps
open import foundation-core.torsorial-type-families

open import logic.double-negation-eliminating-maps
open import logic.double-negation-elimination
```

</details>

## Idea

A [map](foundation-core.function-types.md) is said to be a
{{#concept "double negation stable embedding" Disambiguation="of types" Agda=is-double-negation-stable-emb}}
if it is an [embedding](foundation-core.embeddings.md) and its
[fibers](foundation-core.fibers-of-maps.md) satisfy
[double negation elimination](logic.double-negation-elimination.md).

Equivalently, a double negation stable embedding is a map whose fibers are
[double negation stable propositions](foundation.double-negation-stable-propositions.md).
We refer to this condition as being a
{{#concept "double negation stable propositional map" Disambiguation="of types" Agda=is-double-negation-stable-prop-map}}.

Double negation stable embeddings form the right class of an orthogonal
factorization system on types whose left class is
[double negation dense maps](logic.double-negation-dense-maps.md). This
orthogonal factorization system is determined by the
[double negation modality](foundation.double-negation-modality.md).

## Definitions

### The condition on a map of being a double negation stable embedding

```agda
is-double-negation-stable-emb :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → (X → Y) → UU (l1 ⊔ l2)
is-double-negation-stable-emb f =
  is-emb f × is-double-negation-eliminating-map f

module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : X → Y}
  (F : is-double-negation-stable-emb f)
  where

  is-emb-is-double-negation-stable-emb : is-emb f
  is-emb-is-double-negation-stable-emb = pr1 F

  is-double-negation-eliminating-map-is-double-negation-stable-emb :
    is-double-negation-eliminating-map f
  is-double-negation-eliminating-map-is-double-negation-stable-emb = pr2 F

  is-prop-map-is-double-negation-stable-emb : is-prop-map f
  is-prop-map-is-double-negation-stable-emb =
    is-prop-map-is-emb is-emb-is-double-negation-stable-emb

  is-injective-is-double-negation-stable-emb : is-injective f
  is-injective-is-double-negation-stable-emb =
    is-injective-is-emb is-emb-is-double-negation-stable-emb
```

### Double negation stable propositional maps

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where

  is-double-negation-stable-prop-map : (X → Y) → UU (l1 ⊔ l2)
  is-double-negation-stable-prop-map f =
    (y : Y) → is-double-negation-stable-prop (fiber f y)

  is-prop-is-double-negation-stable-prop-map :
    (f : X → Y) → is-prop (is-double-negation-stable-prop-map f)
  is-prop-is-double-negation-stable-prop-map f =
    is-prop-Π (λ y → is-prop-is-double-negation-stable-prop (fiber f y))

  is-double-negation-stable-prop-map-Prop : (X → Y) → Prop (l1 ⊔ l2)
  is-double-negation-stable-prop-map-Prop f =
    ( is-double-negation-stable-prop-map f ,
      is-prop-is-double-negation-stable-prop-map f)

  is-prop-map-is-double-negation-stable-prop-map :
    {f : X → Y} → is-double-negation-stable-prop-map f → is-prop-map f
  is-prop-map-is-double-negation-stable-prop-map H y = pr1 (H y)

  is-double-negation-eliminating-map-is-double-negation-stable-prop-map :
    {f : X → Y} →
    is-double-negation-stable-prop-map f →
    is-double-negation-eliminating-map f
  is-double-negation-eliminating-map-is-double-negation-stable-prop-map H y =
    pr2 (H y)
```

### The type of double negation stable embeddings

```agda
infix 5 _↪¬¬_
_↪¬¬_ :
  {l1 l2 : Level} (X : UU l1) (Y : UU l2) → UU (l1 ⊔ l2)
X ↪¬¬ Y = Σ (X → Y) is-double-negation-stable-emb

double-negation-stable-emb :
  {l1 l2 : Level} (X : UU l1) (Y : UU l2) → UU (l1 ⊔ l2)
double-negation-stable-emb = _↪¬¬_

module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : X ↪¬¬ Y)
  where

  map-double-negation-stable-emb : X → Y
  map-double-negation-stable-emb = pr1 e

  is-double-negation-stable-emb-map-double-negation-stable-emb :
    is-double-negation-stable-emb map-double-negation-stable-emb
  is-double-negation-stable-emb-map-double-negation-stable-emb = pr2 e

  is-emb-map-double-negation-stable-emb :
    is-emb map-double-negation-stable-emb
  is-emb-map-double-negation-stable-emb =
    is-emb-is-double-negation-stable-emb
      is-double-negation-stable-emb-map-double-negation-stable-emb

  is-double-negation-eliminating-map-map-double-negation-stable-emb :
    is-double-negation-eliminating-map map-double-negation-stable-emb
  is-double-negation-eliminating-map-map-double-negation-stable-emb =
    is-double-negation-eliminating-map-is-double-negation-stable-emb
      is-double-negation-stable-emb-map-double-negation-stable-emb

  emb-double-negation-stable-emb : X ↪ Y
  emb-double-negation-stable-emb =
    map-double-negation-stable-emb , is-emb-map-double-negation-stable-emb
```

## Properties

### Any map of which the fibers are double negation stable propositions is a double negation stable embedding

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : X → Y}
  where

  abstract
    is-double-negation-stable-emb-is-double-negation-stable-prop-map :
      is-double-negation-stable-prop-map f → is-double-negation-stable-emb f
    pr1 (is-double-negation-stable-emb-is-double-negation-stable-prop-map H) =
      is-emb-is-prop-map (is-prop-map-is-double-negation-stable-prop-map H)
    pr2 (is-double-negation-stable-emb-is-double-negation-stable-prop-map H) =
      is-double-negation-eliminating-map-is-double-negation-stable-prop-map H

  abstract
    is-double-negation-stable-prop-map-is-double-negation-stable-emb :
      is-double-negation-stable-emb f → is-double-negation-stable-prop-map f
    pr1 (is-double-negation-stable-prop-map-is-double-negation-stable-emb H y) =
      is-prop-map-is-double-negation-stable-emb H y
    pr2 (is-double-negation-stable-prop-map-is-double-negation-stable-emb H y) =
      is-double-negation-eliminating-map-is-double-negation-stable-emb H y
```

### The first projection map of a dependent sum of double negation stable propositions is a double negation stable embedding

```agda
module _
  {l1 l2 : Level} {A : UU l1} (Q : A → Double-Negation-Stable-Prop l2)
  where

  is-double-negation-stable-prop-map-pr1 :
    is-double-negation-stable-prop-map
      ( pr1 {B = type-Double-Negation-Stable-Prop ∘ Q})
  is-double-negation-stable-prop-map-pr1 y =
    is-double-negation-stable-prop-equiv
      ( equiv-fiber-pr1 (type-Double-Negation-Stable-Prop ∘ Q) y)
      ( is-double-negation-stable-prop-type-Double-Negation-Stable-Prop (Q y))

  is-double-negation-stable-emb-pr1 :
    is-double-negation-stable-emb
      ( pr1 {B = type-Double-Negation-Stable-Prop ∘ Q})
  is-double-negation-stable-emb-pr1 =
    is-double-negation-stable-emb-is-double-negation-stable-prop-map
      ( is-double-negation-stable-prop-map-pr1)
```

### Decidable embeddings are double negation stable

```agda
is-double-negation-eliminating-map-is-decidable-emb :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-decidable-emb f → is-double-negation-eliminating-map f
is-double-negation-eliminating-map-is-decidable-emb H =
  is-double-negation-eliminating-map-is-decidable-map
    ( is-decidable-map-is-decidable-emb H)

abstract
  is-double-negation-stable-emb-is-decidable-emb :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
    is-decidable-emb f → is-double-negation-stable-emb f
  is-double-negation-stable-emb-is-decidable-emb H =
    ( is-emb-is-decidable-emb H ,
      is-double-negation-eliminating-map-is-decidable-emb H)
```

### Equivalences are double negation stable embeddings

```agda
abstract
  is-double-negation-stable-emb-is-equiv :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
    is-equiv f → is-double-negation-stable-emb f
  is-double-negation-stable-emb-is-equiv H =
    ( is-emb-is-equiv H , is-double-negation-eliminating-map-is-equiv H)
```

### Identity maps are double negation stable embeddings

```agda
is-double-negation-stable-emb-id :
  {l : Level} {A : UU l} → is-double-negation-stable-emb (id {A = A})
is-double-negation-stable-emb-id =
  ( is-emb-id , is-double-negation-eliminating-map-id)

double-negation-stable-emb-id : {l : Level} {A : UU l} → A ↪¬¬ A
double-negation-stable-emb-id = (id , is-double-negation-stable-emb-id)

is-double-negation-stable-prop-map-id :
  {l : Level} {A : UU l} → is-double-negation-stable-prop-map (id {A = A})
is-double-negation-stable-prop-map-id y =
  is-double-negation-stable-prop-is-contr (is-torsorial-Id' y)
```

### Being a double negation stable embedding is a property

```agda
abstract
  is-prop-is-double-negation-stable-emb :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-prop (is-double-negation-stable-emb f)
  is-prop-is-double-negation-stable-emb f =
    is-prop-has-element
      ( λ H →
        is-prop-product
          ( is-property-is-emb f)
          ( is-prop-Π
            ( is-prop-has-double-negation-elim ∘ is-prop-map-is-emb (pr1 H))))

is-double-negation-stable-emb-Prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → Prop (l1 ⊔ l2)
is-double-negation-stable-emb-Prop f =
  ( is-double-negation-stable-emb f , is-prop-is-double-negation-stable-emb f)
```

### Double negation stable embeddings are closed under homotopies

```agda
abstract
  is-double-negation-stable-emb-htpy :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f g : A → B} →
    f ~ g → is-double-negation-stable-emb g → is-double-negation-stable-emb f
  is-double-negation-stable-emb-htpy {f = f} {g} H K =
    ( is-emb-htpy H (is-emb-is-double-negation-stable-emb K) ,
      is-double-negation-eliminating-map-htpy H
        ( is-double-negation-eliminating-map-is-double-negation-stable-emb K))
```

### Double negation stable embeddings are closed under composition

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {g : B → C} {f : A → B}
  where

  is-double-negation-eliminating-map-comp-is-double-negation-stable-emb :
    is-double-negation-stable-emb g →
    is-double-negation-eliminating-map f →
    is-double-negation-eliminating-map (g ∘ f)
  is-double-negation-eliminating-map-comp-is-double-negation-stable-emb G F =
    is-double-negation-eliminating-map-comp
      ( is-injective-is-double-negation-stable-emb G)
      ( is-double-negation-eliminating-map-is-double-negation-stable-emb G)
      ( F)

  is-double-negation-stable-prop-map-comp :
    is-double-negation-stable-prop-map g →
    is-double-negation-stable-prop-map f →
    is-double-negation-stable-prop-map (g ∘ f)
  is-double-negation-stable-prop-map-comp K H z =
    is-double-negation-stable-prop-equiv
      ( compute-fiber-comp g f z)
      ( is-double-negation-stable-prop-Σ (K z) (H ∘ pr1))

  is-double-negation-stable-emb-comp :
    is-double-negation-stable-emb g →
    is-double-negation-stable-emb f →
    is-double-negation-stable-emb (g ∘ f)
  is-double-negation-stable-emb-comp K H =
    is-double-negation-stable-emb-is-double-negation-stable-prop-map
      ( is-double-negation-stable-prop-map-comp
        ( is-double-negation-stable-prop-map-is-double-negation-stable-emb K)
        ( is-double-negation-stable-prop-map-is-double-negation-stable-emb H))

comp-double-negation-stable-emb :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} →
  B ↪¬¬ C → A ↪¬¬ B → A ↪¬¬ C
comp-double-negation-stable-emb (g , G) (f , F) =
  ( g ∘ f , is-double-negation-stable-emb-comp G F)

infixr 15 _∘¬¬_
_∘¬¬_ :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} →
  B ↪¬¬ C → A ↪¬¬ B → A ↪¬¬ C
_∘¬¬_ = comp-double-negation-stable-emb
```

### Left cancellation for double negation stable embeddings

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {f : A → B} {g : B → C}
  where

  is-double-negation-stable-emb-right-factor' :
      is-double-negation-stable-emb (g ∘ f) →
      is-emb g →
      is-double-negation-stable-emb f
  is-double-negation-stable-emb-right-factor' GH G =
    ( is-emb-right-factor g f G (is-emb-is-double-negation-stable-emb GH) ,
      is-double-negation-eliminating-map-right-factor'
        ( is-double-negation-eliminating-map-is-double-negation-stable-emb GH)
        ( is-injective-is-emb G))

  is-double-negation-stable-emb-right-factor :
      is-double-negation-stable-emb (g ∘ f) →
      is-double-negation-stable-emb g →
      is-double-negation-stable-emb f
  is-double-negation-stable-emb-right-factor GH G =
    is-double-negation-stable-emb-right-factor'
      ( GH)
      ( is-emb-is-double-negation-stable-emb G)
```

### In a commuting triangle of maps, if the top and right maps are double negation stable embeddings so is the left map

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {top : A → B} {left : A → C} {right : B → C}
  (H : left ~ right ∘ top)
  where

  is-double-negation-stable-emb-left-map-triangle :
    is-double-negation-stable-emb top →
    is-double-negation-stable-emb right →
    is-double-negation-stable-emb left
  is-double-negation-stable-emb-left-map-triangle T R =
    is-double-negation-stable-emb-htpy H
      ( is-double-negation-stable-emb-comp R T)
```

### In a commuting triangle of maps, if the left and right maps are double negation stable embeddings so is the top map

In fact, the right map need only be an embedding.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {top : A → B} {left : A → C} {right : B → C}
  (H : left ~ right ∘ top)
  where

  is-double-negation-stable-emb-top-map-triangle' :
    is-emb right →
    is-double-negation-stable-emb left →
    is-double-negation-stable-emb top
  is-double-negation-stable-emb-top-map-triangle' R' L =
    is-double-negation-stable-emb-right-factor'
      ( is-double-negation-stable-emb-htpy (inv-htpy H) L)
      ( R')

  is-double-negation-stable-emb-top-map-triangle :
    is-double-negation-stable-emb right →
    is-double-negation-stable-emb left →
    is-double-negation-stable-emb top
  is-double-negation-stable-emb-top-map-triangle R L =
    is-double-negation-stable-emb-right-factor
      ( is-double-negation-stable-emb-htpy (inv-htpy H) L)
      ( R)
```

### Characterizing equality in the type of double negation stable embeddings

```agda
htpy-double-negation-stable-emb :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f g : A ↪¬¬ B) → UU (l1 ⊔ l2)
htpy-double-negation-stable-emb f g =
  map-double-negation-stable-emb f ~ map-double-negation-stable-emb g

refl-htpy-double-negation-stable-emb :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A ↪¬¬ B) →
  htpy-double-negation-stable-emb f f
refl-htpy-double-negation-stable-emb f = refl-htpy

htpy-eq-double-negation-stable-emb :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f g : A ↪¬¬ B) →
  f ＝ g → htpy-double-negation-stable-emb f g
htpy-eq-double-negation-stable-emb f .f refl =
  refl-htpy-double-negation-stable-emb f

abstract
  is-torsorial-htpy-double-negation-stable-emb :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A ↪¬¬ B) →
    is-torsorial (htpy-double-negation-stable-emb f)
  is-torsorial-htpy-double-negation-stable-emb f =
    is-torsorial-Eq-subtype
      ( is-torsorial-htpy (map-double-negation-stable-emb f))
      ( is-prop-is-double-negation-stable-emb)
      ( map-double-negation-stable-emb f)
      ( refl-htpy)
      ( is-double-negation-stable-emb-map-double-negation-stable-emb f)

abstract
  is-equiv-htpy-eq-double-negation-stable-emb :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f g : A ↪¬¬ B) →
    is-equiv (htpy-eq-double-negation-stable-emb f g)
  is-equiv-htpy-eq-double-negation-stable-emb f =
    fundamental-theorem-id
      ( is-torsorial-htpy-double-negation-stable-emb f)
      ( htpy-eq-double-negation-stable-emb f)

eq-htpy-double-negation-stable-emb :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f g : A ↪¬¬ B) →
  htpy-double-negation-stable-emb f g → f ＝ g
eq-htpy-double-negation-stable-emb f g =
  map-inv-is-equiv (is-equiv-htpy-eq-double-negation-stable-emb f g)
```

### Precomposing double negation stable embeddings with equivalences

```agda
equiv-precomp-double-negation-stable-emb-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
  (C : UU l3) → (B ↪¬¬ C) ≃ (A ↪¬¬ C)
equiv-precomp-double-negation-stable-emb-equiv e C =
  equiv-Σ
    ( is-double-negation-stable-emb)
    ( equiv-precomp e C)
    ( λ g →
      equiv-iff-is-prop
        ( is-prop-is-double-negation-stable-emb g)
        ( is-prop-is-double-negation-stable-emb (g ∘ map-equiv e))
        ( λ H →
          is-double-negation-stable-emb-comp H
            ( is-double-negation-stable-emb-is-equiv (pr2 e)))
        ( λ d →
          is-double-negation-stable-emb-htpy
            ( λ b → ap g (inv (is-section-map-inv-equiv e b)))
            ( is-double-negation-stable-emb-comp
              ( d)
              ( is-double-negation-stable-emb-is-equiv
                ( is-equiv-map-inv-equiv e)))))
```

### Any map out of the empty type is a double negation stable embedding

```agda
abstract
  is-double-negation-stable-emb-ex-falso :
    {l : Level} {X : UU l} → is-double-negation-stable-emb (ex-falso {l} {X})
  is-double-negation-stable-emb-ex-falso =
    ( is-emb-ex-falso , is-double-negation-eliminating-map-ex-falso)

double-negation-stable-emb-ex-falso :
  {l : Level} {X : UU l} → empty ↪¬¬ X
double-negation-stable-emb-ex-falso =
  ( ex-falso , is-double-negation-stable-emb-ex-falso)

double-negation-stable-emb-is-empty :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → is-empty A → A ↪¬¬ B
double-negation-stable-emb-is-empty {A = A} f =
  map-equiv
    ( equiv-precomp-double-negation-stable-emb-equiv (equiv-is-empty f id) _)
    ( double-negation-stable-emb-ex-falso)
```

### The map on total spaces induced by a family of double negation stable embeddings is a double negation stable embedding

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  where

  is-double-negation-stable-emb-tot :
    {f : (x : A) → B x → C x} →
    ((x : A) → is-double-negation-stable-emb (f x)) →
    is-double-negation-stable-emb (tot f)
  is-double-negation-stable-emb-tot H =
    ( is-emb-tot (is-emb-is-double-negation-stable-emb ∘ H) ,
      is-double-negation-eliminating-map-tot
        ( is-double-negation-eliminating-map-is-double-negation-stable-emb ∘ H))

  double-negation-stable-emb-tot : ((x : A) → B x ↪¬¬ C x) → Σ A B ↪¬¬ Σ A C
  double-negation-stable-emb-tot f =
    ( tot (map-double-negation-stable-emb ∘ f) ,
      is-double-negation-stable-emb-tot
        ( is-double-negation-stable-emb-map-double-negation-stable-emb ∘ f))
```

### The map on total spaces induced by a double negation stable embedding on the base is a double negation stable embedding

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : B → UU l3)
  where

  is-double-negation-stable-emb-map-Σ-map-base :
    {f : A → B} →
    is-double-negation-stable-emb f →
    is-double-negation-stable-emb (map-Σ-map-base f C)
  is-double-negation-stable-emb-map-Σ-map-base H =
    ( is-emb-map-Σ-map-base C (is-emb-is-double-negation-stable-emb H) ,
      is-double-negation-eliminating-map-Σ-map-base C
        ( is-double-negation-eliminating-map-is-double-negation-stable-emb H))

  double-negation-stable-emb-map-Σ-map-base :
    (f : A ↪¬¬ B) → Σ A (C ∘ map-double-negation-stable-emb f) ↪¬¬ Σ B C
  double-negation-stable-emb-map-Σ-map-base f =
    ( map-Σ-map-base (map-double-negation-stable-emb f) C ,
      is-double-negation-stable-emb-map-Σ-map-base
        ( is-double-negation-stable-emb-map-double-negation-stable-emb f))
```

### The functoriality of dependent pair types preserves double negation stable embeddings

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3} (D : B → UU l4)
  where

  is-double-negation-stable-emb-map-Σ :
    {f : A → B} {g : (x : A) → C x → D (f x)} →
    is-double-negation-stable-emb f →
    ((x : A) → is-double-negation-stable-emb (g x)) →
    is-double-negation-stable-emb (map-Σ D f g)
  is-double-negation-stable-emb-map-Σ {f} {g} F G =
    is-double-negation-stable-emb-left-map-triangle
      ( triangle-map-Σ D f g)
      ( is-double-negation-stable-emb-tot G)
      ( is-double-negation-stable-emb-map-Σ-map-base D F)

  double-negation-stable-emb-Σ :
    (f : A ↪¬¬ B) →
    ((x : A) → C x ↪¬¬ D (map-double-negation-stable-emb f x)) →
    Σ A C ↪¬¬ Σ B D
  double-negation-stable-emb-Σ f g =
    ( ( map-Σ D
        ( map-double-negation-stable-emb f)
        ( map-double-negation-stable-emb ∘ g)) ,
      ( is-double-negation-stable-emb-map-Σ
        ( is-double-negation-stable-emb-map-double-negation-stable-emb f)
        ( is-double-negation-stable-emb-map-double-negation-stable-emb ∘ g)))
```

### Products of double negation stable embeddings are double negation stable embeddings

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  where

  is-double-negation-stable-emb-map-product :
    {f : A → B} {g : C → D} →
    is-double-negation-stable-emb f →
    is-double-negation-stable-emb g →
    is-double-negation-stable-emb (map-product f g)
  is-double-negation-stable-emb-map-product (eF , dF) (eG , dG) =
    ( is-emb-map-product eF eG ,
      is-double-negation-eliminating-map-product dF dG)

  double-negation-stable-emb-product :
    A ↪¬¬ B → C ↪¬¬ D → A × C ↪¬¬ B × D
  double-negation-stable-emb-product (f , F) (g , G) =
    ( map-product f g , is-double-negation-stable-emb-map-product F G)
```

### Coproducts of double negation stable embeddings are double negation stable embeddings

```agda
module _
  {l1 l2 l1' l2' : Level} {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
  where

abstract
  is-double-negation-stable-emb-map-coproduct :
    {l1 l2 l3 l4 : Level}
    {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
    {f : A → B} {g : X → Y} →
    is-double-negation-stable-emb f →
    is-double-negation-stable-emb g →
    is-double-negation-stable-emb (map-coproduct f g)
  is-double-negation-stable-emb-map-coproduct (eF , dF) (eG , dG) =
    ( is-emb-map-coproduct eF eG ,
      is-double-negation-eliminating-map-coproduct dF dG)
```

### Double negation stable embeddings are closed under base change

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  {f : A → B} {g : C → D}
  where

  is-double-negation-stable-prop-map-base-change :
    cartesian-hom-arrow g f →
    is-double-negation-stable-prop-map f →
    is-double-negation-stable-prop-map g
  is-double-negation-stable-prop-map-base-change α F d =
    is-double-negation-stable-prop-equiv
      ( equiv-fibers-cartesian-hom-arrow g f α d)
      ( F (map-codomain-cartesian-hom-arrow g f α d))

  is-double-negation-stable-emb-base-change :
    cartesian-hom-arrow g f →
    is-double-negation-stable-emb f →
    is-double-negation-stable-emb g
  is-double-negation-stable-emb-base-change α F =
    is-double-negation-stable-emb-is-double-negation-stable-prop-map
      ( is-double-negation-stable-prop-map-base-change α
        ( is-double-negation-stable-prop-map-is-double-negation-stable-emb F))
```

### Double negation stable embeddings are closed under retracts of arrows

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  {f : A → B} {g : X → Y}
  where

  is-double-negation-stable-prop-map-retract-arrow :
    f retract-of-arrow g →
    is-double-negation-stable-prop-map g →
    is-double-negation-stable-prop-map f
  is-double-negation-stable-prop-map-retract-arrow R G x =
    is-double-negation-stable-prop-retract
      ( retract-fiber-retract-arrow f g R x)
      ( G (map-codomain-inclusion-retract-arrow f g R x))

  is-double-negation-stable-emb-retract-arrow :
    f retract-of-arrow g →
    is-double-negation-stable-emb g →
    is-double-negation-stable-emb f
  is-double-negation-stable-emb-retract-arrow R G =
    is-double-negation-stable-emb-is-double-negation-stable-prop-map
      ( is-double-negation-stable-prop-map-retract-arrow R
        ( is-double-negation-stable-prop-map-is-double-negation-stable-emb G))
```

### A type is a double negation stable proposition if and only if its terminal map is a double negation stable embedding

```agda
module _
  {l : Level} {A : UU l}
  where

  is-double-negation-stable-prop-is-double-negation-stable-emb-terminal-map :
    is-double-negation-stable-emb (terminal-map A) →
    is-double-negation-stable-prop A
  is-double-negation-stable-prop-is-double-negation-stable-emb-terminal-map H =
    is-double-negation-stable-prop-equiv'
      ( equiv-fiber-terminal-map star)
      ( is-double-negation-stable-prop-map-is-double-negation-stable-emb H star)

  is-double-negation-stable-emb-terminal-map-is-double-negation-stable-prop :
    is-double-negation-stable-prop A →
    is-double-negation-stable-emb (terminal-map A)
  is-double-negation-stable-emb-terminal-map-is-double-negation-stable-prop H =
    is-double-negation-stable-emb-is-double-negation-stable-prop-map
      ( λ y →
        is-double-negation-stable-prop-equiv (equiv-fiber-terminal-map y) H)
```

### If a dependent sum of propositions over a proposition is double negation stable, then the family is a family of double negation stable propositions

```agda
module _
  {l1 l2 : Level} (P : Prop l1) (Q : type-Prop P → Prop l2)
  where

  is-double-negation-stable-prop-family-has-double-negation-elim-Σ :
    has-double-negation-elim (Σ (type-Prop P) (type-Prop ∘ Q)) →
    (p : type-Prop P) → has-double-negation-elim (type-Prop (Q p))
  is-double-negation-stable-prop-family-has-double-negation-elim-Σ H p =
    has-double-negation-elim-equiv'
      ( equiv-fiber-pr1 (type-Prop ∘ Q) p)
      ( is-double-negation-eliminating-map-is-double-negation-stable-emb
        ( is-double-negation-stable-emb-right-factor'
          ( is-double-negation-stable-emb-terminal-map-is-double-negation-stable-prop
            ( is-prop-Σ (is-prop-type-Prop P) (is-prop-type-Prop ∘ Q) , H))
          ( is-emb-terminal-map-is-prop (is-prop-type-Prop P)))
          ( p))
```

## See also

- [Double negation images](foundation.double-negation-images.md)
