# Weakly constant maps

```agda
module foundation.weakly-constant-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.fixed-points-endofunctions
open import foundation.identity-types
open import foundation.iterated-dependent-product-types
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.propositions
open import foundation-core.sets
open import foundation-core.torsorial-type-families
```

</details>

## Idea

A map `f : A → B` is said to be
{{#concept "weakly constant" Disambiguation="map of types" Agda=is-weakly-constant-map}}
if any two elements in `A` are mapped to
[identical elements](foundation-core.identity-types.md) in `B`.

## Definitions

### The structure on a map of being weakly constant

```agda
is-weakly-constant-map :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
is-weakly-constant-map {A = A} f = (x y : A) → f x ＝ f y
```

### The type of weakly constant maps

```agda
weakly-constant-map : {l1 l2 : Level} (A : UU l1) (B : UU l2) → UU (l1 ⊔ l2)
weakly-constant-map A B = Σ (A → B) (is-weakly-constant-map)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : weakly-constant-map A B)
  where

  map-weakly-constant-map : A → B
  map-weakly-constant-map = pr1 f

  is-weakly-constant-weakly-constant-map :
    is-weakly-constant-map map-weakly-constant-map
  is-weakly-constant-weakly-constant-map = pr2 f
```

## Properties

### Being weakly constant is a property if the codomain is a set

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Set l2) (f : A → type-Set B)
  where

  abstract
    is-prop-is-weakly-constant-map-Set : is-prop (is-weakly-constant-map f)
    is-prop-is-weakly-constant-map-Set =
      is-prop-iterated-Π 2 (λ x y → is-set-type-Set B (f x) (f y))

  is-weakly-constant-map-prop-Set : Prop (l1 ⊔ l2)
  pr1 is-weakly-constant-map-prop-Set = is-weakly-constant-map f
  pr2 is-weakly-constant-map-prop-Set = is-prop-is-weakly-constant-map-Set
```

### The action on identifications of a weakly constant map is weakly constant

This is Auxiliary Lemma 4.3 of {{#cite KECA17}}.

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : X → Y}
  (W : is-weakly-constant-map f)
  where

  compute-ap-is-weakly-constant-map :
    {x y : X} (p : x ＝ y) → inv (W x x) ∙ W x y ＝ ap f p
  compute-ap-is-weakly-constant-map {x} refl = left-inv (W x x)

  is-weakly-constant-ap : {x y : X} → is-weakly-constant-map (ap f {x} {y})
  is-weakly-constant-ap {x} {y} p q =
    ( inv (compute-ap-is-weakly-constant-map p)) ∙
    ( compute-ap-is-weakly-constant-map q)

module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  (f : weakly-constant-map X Y)
  where

  ap-weakly-constant-map :
    {x y : X} →
    weakly-constant-map
      ( x ＝ y)
      ( map-weakly-constant-map f x ＝ map-weakly-constant-map f y)
  ap-weakly-constant-map {x} {y} =
    ( ap (map-weakly-constant-map f) {x} {y} ,
      is-weakly-constant-ap (is-weakly-constant-weakly-constant-map f))
```

### The type of fixed points of a weakly constant endomap is a proposition

This is Lemma 4.1 of {{#cite KECA17}}. We follow the second proof, due to
Christian Sattler.

```agda
module _
  {l : Level} {A : UU l} {f : A → A} (W : is-weakly-constant-map f)
  where

  is-proof-irrelevant-fixed-point-is-weakly-constant-map :
    is-proof-irrelevant (fixed-point f)
  is-proof-irrelevant-fixed-point-is-weakly-constant-map (x , p) =
    is-contr-equiv
      ( Σ A (λ z → f x ＝ z))
      ( equiv-tot (λ z → equiv-concat (W x z) z))
      ( is-torsorial-Id (f x))

  is-prop-fixed-point-is-weakly-constant-map : is-prop (fixed-point f)
  is-prop-fixed-point-is-weakly-constant-map =
    is-prop-is-proof-irrelevant
      ( is-proof-irrelevant-fixed-point-is-weakly-constant-map)
```

## References

{{#bibliography}} {{#reference KECA17}}
