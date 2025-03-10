# Anodyne maps

```agda
module orthogonal-factorization-systems.anodyne-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-morphisms-arrows
open import foundation.cartesian-product-types
open import foundation.composition-algebra
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.coproducts-pullbacks
open import foundation.dependent-pair-types
open import foundation.dependent-products-pullbacks
open import foundation.dependent-sums-pullbacks
open import foundation.equivalences
open import foundation.equivalences-arrows
open import foundation.fibered-maps
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-fibers-of-maps
open import foundation.homotopies
open import foundation.morphisms-arrows
open import foundation.postcomposition-functions
open import foundation.postcomposition-pullbacks
open import foundation.precomposition-dependent-functions
open import foundation.precomposition-functions
open import foundation.products-pullbacks
open import foundation.propositions
open import foundation.pullbacks
open import foundation.retracts-of-maps
open import foundation.type-arithmetic-dependent-function-types
open import foundation.type-theoretic-principle-of-choice
open import foundation.unit-type
open import foundation.universal-property-cartesian-product-types
open import foundation.universal-property-coproduct-types
open import foundation.universal-property-dependent-pair-types
open import foundation.universal-property-equivalences
open import foundation.universal-property-pullbacks
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import orthogonal-factorization-systems.lifting-structures-on-squares
open import orthogonal-factorization-systems.orthogonal-maps
open import orthogonal-factorization-systems.pullback-hom
open import orthogonal-factorization-systems.types-local-at-maps

open import synthetic-homotopy-theory.cocartesian-morphisms-arrows
```

</details>

## Idea

A map $j : C → D$ is said to be
{{#concept "anodyne" Disambiguation="map of types" Agda=is-anodyne}} with
respect to a map $f : A → B$, or **$f$-anodyne** if every map that is orthogonal
to $f$ is also orthogonal to $j$.

## Definitions

### The predicate of being anodyne with respect to a map

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (j : C → D)
  where

  is-anodyne-Level :
    (l5 l6 : Level) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ lsuc l5 ⊔ lsuc l6)
  is-anodyne-Level l5 l6 =
    {X : UU l5} {Y : UU l6} (g : X → Y) → is-orthogonal f g → is-orthogonal j g

  is-anodyne : UUω
  is-anodyne = {l5 l6 : Level} → is-anodyne-Level l5 l6
```

## Properties

### Anodyne maps are closed under homotopies

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) {j i : C → D}
  where

  is-anodyne-htpy : j ~ i → is-anodyne f j → is-anodyne f i
  is-anodyne-htpy K J g H = is-orthogonal-htpy-left j g K (J g H)
```

### Anodyne maps are closed under equivalences of maps

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4} {C' : UU l5} {D' : UU l6}
  (f : A → B) {j : C → D} {j' : C' → D'}
  where

  is-anodyne-equiv-arrow : equiv-arrow j j' → is-anodyne f j → is-anodyne f j'
  is-anodyne-equiv-arrow α J g H = is-orthogonal-left-equiv-arrow α g (J g H)
```

### Anodyne maps are closed under retracts of maps

> This remains to be formalized.

### Anodyne maps compose

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4} {E : UU l5}
  (f : A → B) (j : C → D) (i : D → E)
  where

  is-anodyne-comp : is-anodyne f j → is-anodyne f i → is-anodyne f (i ∘ j)
  is-anodyne-comp J I g H = is-orthogonal-left-comp j i g (J g H) (I g H)
```

### Cancellation property for anodyne maps

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4} {E : UU l5}
  (f : A → B) (j : C → D) (i : D → E)
  where

  is-anodyne-left-factor :
    is-anodyne f j → is-anodyne f (i ∘ j) → is-anodyne f i
  is-anodyne-left-factor J IJ g H =
    is-orthogonal-left-left-factor j i g (J g H) (IJ g H)
```

### Anodyne maps are closed under dependent sums

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} {B : UU l2} {I : UU l3} {C : I → UU l4} {D : I → UU l5}
  (f : A → B) (j : (i : I) → C i → D i)
  where

  is-anodyne-tot : ((i : I) → is-anodyne f (j i)) → is-anodyne f (tot j)
  is-anodyne-tot J g H = is-orthogonal-left-tot j g (λ i → J i g H)
```

### Anodyne maps are closed under products

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4} {E : UU l5} {F : UU l6}
  (f : A → B) (j : C → D) (i : E → F)
  where

  is-anodyne-map-product :
    is-anodyne f j → is-anodyne f i → is-anodyne f (map-product j i)
  is-anodyne-map-product J I g H =
    is-orthogonal-left-product j i g (J g H) (I g H)
```

### Anodyne maps are closed under coproducts

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4} {E : UU l5} {F : UU l6}
  (f : A → B) (j : C → D) (i : E → F)
  where

  is-anodyne-map-coproduct :
    is-anodyne f j → is-anodyne f i → is-anodyne f (map-coproduct j i)
  is-anodyne-map-coproduct J I g H =
    is-orthogonal-left-coproduct j i g (J g H) (I g H)
```

### Anodyne maps are closed under cobase change

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4} {E : UU l5} {F : UU l6}
  (f : A → B) (j : C → D) (i : E → F)
  where

  is-anodyne-cobase-change :
    cocartesian-hom-arrow j i → is-anodyne f j → is-anodyne f i
  is-anodyne-cobase-change α J g H =
    is-orthogonal-left-cobase-change j i g α (J g H)
```

### Anodyne maps are closed under pushout-products

> This remains to be formalized.
