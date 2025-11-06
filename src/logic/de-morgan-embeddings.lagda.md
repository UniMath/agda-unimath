# De Morgan embeddings

```agda
module logic.de-morgan-embeddings where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-morphisms-arrows
open import foundation.decidable-embeddings
open import foundation.decidable-maps
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.fibers-of-maps
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-coproduct-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositional-maps
open import foundation.propositions
open import foundation.retracts-of-maps
open import foundation.subtype-identity-principle
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.unit-type
open import foundation.universal-property-equivalences
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.coproduct-types
open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.injective-maps
open import foundation-core.torsorial-type-families

open import logic.de-morgan-maps
open import logic.de-morgan-propositions
open import logic.de-morgan-types
open import logic.double-negation-eliminating-maps
open import logic.double-negation-elimination
```

</details>

## Idea

A [map](foundation-core.function-types.md) is said to be a
{{#concept "De Morgan embedding" Disambiguation="of types" Agda=is-de-morgan-emb}}
if it is an [embedding](foundation-core.embeddings.md) and the
[negations](foundation-core.negation.md) of its
[fibers](foundation-core.fibers-of-maps.md) are
[decidable](foundation.decidable-maps.md).

Equivalently, a De Morgan embedding is a map whose fibers are
[De Morgan propositions](logic.de-morgan-propositions.md). We refer to this
condition as being a
{{#concept "De Morgan propositional map" Disambiguation="of types" Agda=is-de-morgan-prop-map}}.

## Definitions

### The condition on a map of being a De Morgan embedding

```agda
is-de-morgan-emb :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → (X → Y) → UU (l1 ⊔ l2)
is-de-morgan-emb f = is-emb f × is-de-morgan-map f

module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : X → Y}
  (F : is-de-morgan-emb f)
  where

  is-emb-is-de-morgan-emb : is-emb f
  is-emb-is-de-morgan-emb = pr1 F

  is-de-morgan-map-is-de-morgan-emb :
    is-de-morgan-map f
  is-de-morgan-map-is-de-morgan-emb = pr2 F

  is-prop-map-is-de-morgan-emb : is-prop-map f
  is-prop-map-is-de-morgan-emb =
    is-prop-map-is-emb is-emb-is-de-morgan-emb

  is-injective-is-de-morgan-emb : is-injective f
  is-injective-is-de-morgan-emb =
    is-injective-is-emb is-emb-is-de-morgan-emb
```

### De Morgan propositional maps

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where

  is-de-morgan-prop-map : (X → Y) → UU (l1 ⊔ l2)
  is-de-morgan-prop-map f =
    (y : Y) → is-de-morgan-prop (fiber f y)

  is-prop-is-de-morgan-prop-map :
    (f : X → Y) → is-prop (is-de-morgan-prop-map f)
  is-prop-is-de-morgan-prop-map f =
    is-prop-Π (λ y → is-prop-is-de-morgan-prop (fiber f y))

  is-de-morgan-prop-map-Prop : (X → Y) → Prop (l1 ⊔ l2)
  is-de-morgan-prop-map-Prop f =
    ( is-de-morgan-prop-map f , is-prop-is-de-morgan-prop-map f)

  is-prop-map-is-de-morgan-prop-map :
    {f : X → Y} → is-de-morgan-prop-map f → is-prop-map f
  is-prop-map-is-de-morgan-prop-map H y =
    is-prop-type-is-de-morgan-prop (H y)

  is-de-morgan-map-is-de-morgan-prop-map :
    {f : X → Y} → is-de-morgan-prop-map f → is-de-morgan-map f
  is-de-morgan-map-is-de-morgan-prop-map H y =
    is-de-morgan-type-is-de-morgan-prop (H y)
```

### The type of De Morgan embeddings

```agda
infix 5 _↪ᵈᵐ_
_↪ᵈᵐ_ : {l1 l2 : Level} (X : UU l1) (Y : UU l2) → UU (l1 ⊔ l2)
X ↪ᵈᵐ Y = Σ (X → Y) (is-de-morgan-emb)

de-morgan-emb : {l1 l2 : Level} (X : UU l1) (Y : UU l2) → UU (l1 ⊔ l2)
de-morgan-emb = _↪ᵈᵐ_

module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : X ↪ᵈᵐ Y)
  where

  map-de-morgan-emb : X → Y
  map-de-morgan-emb = pr1 e

  is-de-morgan-emb-map-de-morgan-emb : is-de-morgan-emb map-de-morgan-emb
  is-de-morgan-emb-map-de-morgan-emb = pr2 e

  is-emb-map-de-morgan-emb : is-emb map-de-morgan-emb
  is-emb-map-de-morgan-emb =
    is-emb-is-de-morgan-emb is-de-morgan-emb-map-de-morgan-emb

  is-de-morgan-map-map-de-morgan-emb : is-de-morgan-map map-de-morgan-emb
  is-de-morgan-map-map-de-morgan-emb =
    is-de-morgan-map-is-de-morgan-emb is-de-morgan-emb-map-de-morgan-emb

  emb-de-morgan-emb : X ↪ Y
  emb-de-morgan-emb = map-de-morgan-emb , is-emb-map-de-morgan-emb
```

## Properties

### Any map of which the fibers are De Morgan propositions is a De Morgan embedding

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : X → Y}
  where

  abstract
    is-de-morgan-emb-is-de-morgan-prop-map :
      is-de-morgan-prop-map f → is-de-morgan-emb f
    pr1 (is-de-morgan-emb-is-de-morgan-prop-map H) =
      is-emb-is-prop-map (is-prop-map-is-de-morgan-prop-map H)
    pr2 (is-de-morgan-emb-is-de-morgan-prop-map H) =
      is-de-morgan-map-is-de-morgan-prop-map H

  abstract
    is-de-morgan-prop-map-is-de-morgan-emb :
      is-de-morgan-emb f → is-de-morgan-prop-map f
    pr1 (is-de-morgan-prop-map-is-de-morgan-emb H y) =
      is-prop-map-is-de-morgan-emb H y
    pr2 (is-de-morgan-prop-map-is-de-morgan-emb H y) =
      is-de-morgan-map-is-de-morgan-emb H y
```

### The first projection map of a dependent sum of De Morgan propositions is a De Morgan embedding

```agda
module _
  {l1 l2 : Level} {A : UU l1} (Q : A → De-Morgan-Prop l2)
  where

  is-de-morgan-prop-map-pr1 :
    is-de-morgan-prop-map
      ( pr1 {B = type-De-Morgan-Prop ∘ Q})
  is-de-morgan-prop-map-pr1 y =
    is-de-morgan-prop-equiv
      ( equiv-fiber-pr1 (type-De-Morgan-Prop ∘ Q) y)
      ( is-de-morgan-prop-type-De-Morgan-Prop (Q y))

  is-de-morgan-emb-pr1 :
    is-de-morgan-emb
      ( pr1 {B = type-De-Morgan-Prop ∘ Q})
  is-de-morgan-emb-pr1 =
    is-de-morgan-emb-is-de-morgan-prop-map
      ( is-de-morgan-prop-map-pr1)
```

### Decidable embeddings are De Morgan

```agda
is-de-morgan-map-is-decidable-emb :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-decidable-emb f → is-de-morgan-map f
is-de-morgan-map-is-decidable-emb H =
  is-de-morgan-map-is-decidable-map
    ( is-decidable-map-is-decidable-emb H)

abstract
  is-de-morgan-emb-is-decidable-emb :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
    is-decidable-emb f → is-de-morgan-emb f
  is-de-morgan-emb-is-decidable-emb H =
    ( is-emb-is-decidable-emb H ,
      is-de-morgan-map-is-decidable-emb H)
```

### Equivalences are De Morgan embeddings

```agda
abstract
  is-de-morgan-emb-is-equiv :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
    is-equiv f → is-de-morgan-emb f
  is-de-morgan-emb-is-equiv H =
    ( is-emb-is-equiv H , is-de-morgan-map-is-equiv H)
```

### Identity maps are De Morgan embeddings

```agda
is-de-morgan-emb-id :
  {l : Level} {A : UU l} → is-de-morgan-emb (id {A = A})
is-de-morgan-emb-id =
  ( is-emb-id , is-de-morgan-map-id)

de-morgan-emb-id : {l : Level} {A : UU l} → A ↪ᵈᵐ A
de-morgan-emb-id = (id , is-de-morgan-emb-id)

is-de-morgan-prop-map-id :
  {l : Level} {A : UU l} → is-de-morgan-prop-map (id {A = A})
is-de-morgan-prop-map-id y =
  is-de-morgan-prop-is-contr (is-torsorial-Id' y)
```

### Being a De Morgan embedding is a property

```agda
abstract
  is-prop-is-de-morgan-emb :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-prop (is-de-morgan-emb f)
  is-prop-is-de-morgan-emb f =
    is-prop-product (is-property-is-emb f) is-prop-is-de-morgan-map
```

### De Morgan embeddings are closed under homotopies

```agda
abstract
  is-de-morgan-emb-htpy :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f g : A → B} →
    f ~ g → is-de-morgan-emb g → is-de-morgan-emb f
  is-de-morgan-emb-htpy {f = f} {g} H K =
    ( is-emb-htpy H (is-emb-is-de-morgan-emb K) ,
      is-de-morgan-map-htpy H
        ( is-de-morgan-map-is-de-morgan-emb K))
```

### De Morgan embeddings are closed under composition

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {g : B → C} {f : A → B}
  where

  is-de-morgan-map-comp-is-decidable-emb :
    is-decidable-emb g →
    is-de-morgan-map f →
    is-de-morgan-map (g ∘ f)
  is-de-morgan-map-comp-is-decidable-emb G F =
    is-de-morgan-map-comp-is-decidable-map
      ( is-injective-is-decidable-emb G)
      ( is-decidable-map-is-decidable-emb G)
      ( F)

  is-de-morgan-prop-map-comp-is-decidable-prop-map :
    is-decidable-prop-map g →
    is-de-morgan-prop-map f →
    is-de-morgan-prop-map (g ∘ f)
  is-de-morgan-prop-map-comp-is-decidable-prop-map K H z =
    is-de-morgan-prop-equiv
      ( compute-fiber-comp g f z)
      ( is-de-morgan-prop-Σ (K z) (H ∘ pr1))

  is-de-morgan-emb-comp-is-decidable-emb :
    is-decidable-emb g →
    is-de-morgan-emb f →
    is-de-morgan-emb (g ∘ f)
  is-de-morgan-emb-comp-is-decidable-emb K H =
    is-de-morgan-emb-is-de-morgan-prop-map
      ( is-de-morgan-prop-map-comp-is-decidable-prop-map
        ( is-decidable-prop-map-is-decidable-emb K)
        ( is-de-morgan-prop-map-is-de-morgan-emb H))

comp-de-morgan-emb :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} →
  B ↪ᵈ C → A ↪ᵈᵐ B → A ↪ᵈᵐ C
comp-de-morgan-emb (g , G) (f , F) =
  ( g ∘ f , is-de-morgan-emb-comp-is-decidable-emb G F)
```

### Left cancellation for De Morgan embeddings

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {f : A → B} {g : B → C}
  where

  is-de-morgan-emb-right-factor' :
      is-de-morgan-emb (g ∘ f) →
      is-emb g →
      is-de-morgan-emb f
  is-de-morgan-emb-right-factor' GF G =
    ( is-emb-right-factor g f G (is-emb-is-de-morgan-emb GF) ,
      is-de-morgan-map-right-factor'
        ( is-injective-is-emb G)
        ( is-de-morgan-map-is-de-morgan-emb GF))

  is-de-morgan-emb-right-factor :
      is-de-morgan-emb (g ∘ f) →
      is-de-morgan-emb g →
      is-de-morgan-emb f
  is-de-morgan-emb-right-factor GF G =
    is-de-morgan-emb-right-factor'
      ( GF)
      ( is-emb-is-de-morgan-emb G)
```

### In a commuting triangle of maps, if the top and right maps are De Morgan embeddings so is the left map

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {top : A → B} {left : A → C} {right : B → C}
  (H : left ~ right ∘ top)
  where

  is-de-morgan-emb-left-map-triangle-is-decidable-emb-top :
    is-de-morgan-emb top →
    is-decidable-emb right →
    is-de-morgan-emb left
  is-de-morgan-emb-left-map-triangle-is-decidable-emb-top T R =
    is-de-morgan-emb-htpy H (is-de-morgan-emb-comp-is-decidable-emb R T)
```

### In a commuting triangle of maps, if the left and right maps are De Morgan embeddings so is the top map

In fact, the right map need only be an embedding.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {top : A → B} {left : A → C} {right : B → C}
  (H : left ~ right ∘ top)
  where

  is-de-morgan-emb-top-map-triangle' :
    is-emb right →
    is-de-morgan-emb left →
    is-de-morgan-emb top
  is-de-morgan-emb-top-map-triangle' R' L =
    is-de-morgan-emb-right-factor'
      ( is-de-morgan-emb-htpy (inv-htpy H) L)
      ( R')

  is-de-morgan-emb-top-map-triangle :
    is-de-morgan-emb right →
    is-de-morgan-emb left →
    is-de-morgan-emb top
  is-de-morgan-emb-top-map-triangle R L =
    is-de-morgan-emb-right-factor
      ( is-de-morgan-emb-htpy (inv-htpy H) L)
      ( R)
```

### Characterizing equality in the type of De Morgan embeddings

```agda
htpy-de-morgan-emb :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f g : A ↪ᵈᵐ B) → UU (l1 ⊔ l2)
htpy-de-morgan-emb f g =
  map-de-morgan-emb f ~ map-de-morgan-emb g

refl-htpy-de-morgan-emb :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A ↪ᵈᵐ B) →
  htpy-de-morgan-emb f f
refl-htpy-de-morgan-emb f = refl-htpy

htpy-eq-de-morgan-emb :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f g : A ↪ᵈᵐ B) →
  f ＝ g → htpy-de-morgan-emb f g
htpy-eq-de-morgan-emb f .f refl =
  refl-htpy-de-morgan-emb f

abstract
  is-torsorial-htpy-de-morgan-emb :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A ↪ᵈᵐ B) →
    is-torsorial (htpy-de-morgan-emb f)
  is-torsorial-htpy-de-morgan-emb f =
    is-torsorial-Eq-subtype
      ( is-torsorial-htpy (map-de-morgan-emb f))
      ( is-prop-is-de-morgan-emb)
      ( map-de-morgan-emb f)
      ( refl-htpy)
      ( is-de-morgan-emb-map-de-morgan-emb f)

abstract
  is-equiv-htpy-eq-de-morgan-emb :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f g : A ↪ᵈᵐ B) →
    is-equiv (htpy-eq-de-morgan-emb f g)
  is-equiv-htpy-eq-de-morgan-emb f =
    fundamental-theorem-id
      ( is-torsorial-htpy-de-morgan-emb f)
      ( htpy-eq-de-morgan-emb f)

eq-htpy-de-morgan-emb :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f g : A ↪ᵈᵐ B) →
  htpy-de-morgan-emb f g → f ＝ g
eq-htpy-de-morgan-emb f g =
  map-inv-is-equiv (is-equiv-htpy-eq-de-morgan-emb f g)
```

### Any map out of the empty type is a De Morgan embedding

```agda
abstract
  is-de-morgan-emb-ex-falso :
    {l : Level} {X : UU l} → is-de-morgan-emb (ex-falso {l} {X})
  is-de-morgan-emb-ex-falso =
    ( is-emb-ex-falso , is-de-morgan-map-ex-falso)

de-morgan-emb-ex-falso :
  {l : Level} {X : UU l} → empty ↪ᵈᵐ X
de-morgan-emb-ex-falso =
  ( ex-falso , is-de-morgan-emb-ex-falso)
```

### The map on total spaces induced by a family of De Morgan embeddings is a De Morgan embedding

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  where

  is-de-morgan-emb-tot :
    {f : (x : A) → B x → C x} →
    ((x : A) → is-de-morgan-emb (f x)) →
    is-de-morgan-emb (tot f)
  is-de-morgan-emb-tot H =
    ( is-emb-tot (is-emb-is-de-morgan-emb ∘ H) ,
      is-de-morgan-map-tot
        ( is-de-morgan-map-is-de-morgan-emb ∘ H))

  de-morgan-emb-tot : ((x : A) → B x ↪ᵈᵐ C x) → Σ A B ↪ᵈᵐ Σ A C
  de-morgan-emb-tot f =
    ( tot (map-de-morgan-emb ∘ f) ,
      is-de-morgan-emb-tot
        ( is-de-morgan-emb-map-de-morgan-emb ∘ f))
```

### The map on total spaces induced by a De Morgan embedding on the base is a De Morgan embedding

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : B → UU l3)
  where

  is-de-morgan-emb-map-Σ-map-base :
    {f : A → B} →
    is-de-morgan-emb f →
    is-de-morgan-emb (map-Σ-map-base f C)
  is-de-morgan-emb-map-Σ-map-base H =
    ( is-emb-map-Σ-map-base C (is-emb-is-de-morgan-emb H) ,
      is-de-morgan-map-Σ-map-base C
        ( is-de-morgan-map-is-de-morgan-emb H))

  de-morgan-emb-map-Σ-map-base :
    (f : A ↪ᵈᵐ B) → Σ A (C ∘ map-de-morgan-emb f) ↪ᵈᵐ Σ B C
  de-morgan-emb-map-Σ-map-base f =
    ( map-Σ-map-base (map-de-morgan-emb f) C ,
      is-de-morgan-emb-map-Σ-map-base
        ( is-de-morgan-emb-map-de-morgan-emb f))
```

### The functoriality of dependent pair types on De Morgan embeddings

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3} (D : B → UU l4)
  where

  is-de-morgan-emb-map-Σ :
    {f : A → B} {g : (x : A) → C x → D (f x)} →
    is-decidable-emb f →
    ((x : A) → is-de-morgan-emb (g x)) →
    is-de-morgan-emb (map-Σ D f g)
  is-de-morgan-emb-map-Σ {f} {g} F G =
    is-de-morgan-emb-left-map-triangle-is-decidable-emb-top
      ( triangle-map-Σ D f g)
      ( is-de-morgan-emb-tot G)
      ( is-decidable-emb-map-Σ-map-base D F)

  de-morgan-emb-Σ :
    (f : A ↪ᵈ B) →
    ((x : A) → C x ↪ᵈᵐ D (map-decidable-emb f x)) →
    Σ A C ↪ᵈᵐ Σ B D
  de-morgan-emb-Σ f g =
    ( ( map-Σ D (map-decidable-emb f) (map-de-morgan-emb ∘ g)) ,
      ( is-de-morgan-emb-map-Σ
        ( is-decidable-emb-map-decidable-emb f)
        ( is-de-morgan-emb-map-de-morgan-emb ∘ g)))
```

### Products of De Morgan embeddings are De Morgan embeddings

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  where

  is-de-morgan-emb-map-product :
    {f : A → B} {g : C → D} →
    is-de-morgan-emb f →
    is-de-morgan-emb g →
    is-de-morgan-emb (map-product f g)
  is-de-morgan-emb-map-product (eF , dF) (eG , dG) =
    ( is-emb-map-product eF eG ,
      is-de-morgan-map-product dF dG)

  de-morgan-emb-product :
    A ↪ᵈᵐ B → C ↪ᵈᵐ D → A × C ↪ᵈᵐ B × D
  de-morgan-emb-product (f , F) (g , G) =
    ( map-product f g , is-de-morgan-emb-map-product F G)
```

### Coproducts of De Morgan embeddings are De Morgan embeddings

```agda
module _
  {l1 l2 l1' l2' : Level} {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
  where

abstract
  is-de-morgan-emb-map-coproduct :
    {l1 l2 l3 l4 : Level}
    {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
    {f : A → B} {g : X → Y} →
    is-de-morgan-emb f →
    is-de-morgan-emb g →
    is-de-morgan-emb (map-coproduct f g)
  is-de-morgan-emb-map-coproduct (eF , dF) (eG , dG) =
    ( is-emb-map-coproduct eF eG ,
      is-de-morgan-map-coproduct dF dG)
```

### De Morgan embeddings are closed under base change

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  {f : A → B} {g : C → D}
  where

  is-de-morgan-prop-map-base-change :
    cartesian-hom-arrow g f →
    is-de-morgan-prop-map f →
    is-de-morgan-prop-map g
  is-de-morgan-prop-map-base-change α F d =
    is-de-morgan-prop-equiv
      ( equiv-fibers-cartesian-hom-arrow g f α d)
      ( F (map-codomain-cartesian-hom-arrow g f α d))

  is-de-morgan-emb-base-change :
    cartesian-hom-arrow g f →
    is-de-morgan-emb f →
    is-de-morgan-emb g
  is-de-morgan-emb-base-change α F =
    is-de-morgan-emb-is-de-morgan-prop-map
      ( is-de-morgan-prop-map-base-change α
        ( is-de-morgan-prop-map-is-de-morgan-emb F))
```

### De Morgan embeddings are closed under retracts of maps

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  {f : A → B} {g : X → Y}
  where

  is-de-morgan-prop-map-retract-map :
    f retract-of-map g →
    is-de-morgan-prop-map g →
    is-de-morgan-prop-map f
  is-de-morgan-prop-map-retract-map R G x =
    is-de-morgan-prop-retract-of
      ( retract-fiber-retract-map f g R x)
      ( G (map-codomain-inclusion-retract-map f g R x))

  is-de-morgan-emb-retract-map :
    f retract-of-map g →
    is-de-morgan-emb g →
    is-de-morgan-emb f
  is-de-morgan-emb-retract-map R G =
    is-de-morgan-emb-is-de-morgan-prop-map
      ( is-de-morgan-prop-map-retract-map R
        ( is-de-morgan-prop-map-is-de-morgan-emb G))
```

### A type is a De Morgan proposition if and only if its terminal map is a De Morgan embedding

```agda
module _
  {l : Level} {A : UU l}
  where

  is-de-morgan-prop-is-de-morgan-emb-terminal-map :
    is-de-morgan-emb (terminal-map A) →
    is-de-morgan-prop A
  is-de-morgan-prop-is-de-morgan-emb-terminal-map H =
    is-de-morgan-prop-equiv'
      ( equiv-fiber-terminal-map star)
      ( is-de-morgan-prop-map-is-de-morgan-emb H star)

  is-de-morgan-emb-terminal-map-is-de-morgan-prop :
    is-de-morgan-prop A →
    is-de-morgan-emb (terminal-map A)
  is-de-morgan-emb-terminal-map-is-de-morgan-prop H =
    is-de-morgan-emb-is-de-morgan-prop-map
      ( λ y →
        is-de-morgan-prop-equiv (equiv-fiber-terminal-map y) H)
```

### If a dependent sum of propositions over a proposition is De Morgan, then the family is a family of De Morgan propositions

```agda
module _
  {l1 l2 : Level} (P : Prop l1) (Q : type-Prop P → Prop l2)
  where

  is-de-morgan-prop-family-is-de-morgan-Σ :
    is-de-morgan (Σ (type-Prop P) (type-Prop ∘ Q)) →
    (p : type-Prop P) → is-de-morgan (type-Prop (Q p))
  is-de-morgan-prop-family-is-de-morgan-Σ H p =
    is-de-morgan-equiv'
      ( equiv-fiber-pr1 (type-Prop ∘ Q) p)
      ( is-de-morgan-map-is-de-morgan-emb
        ( is-de-morgan-emb-right-factor'
          ( is-de-morgan-emb-terminal-map-is-de-morgan-prop
            ( is-prop-Σ (is-prop-type-Prop P) (is-prop-type-Prop ∘ Q) , H))
          ( is-emb-terminal-map-is-prop (is-prop-type-Prop P)))
          ( p))
```
