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
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.propositions
open import foundation-core.sets
open import foundation-core.torsorial-type-families
```

</details>

## Idea

A map `f : A → B` is said to be
{{#concept "weakly constant" Disambiguation="map of types" Agda=is-weakly-constant-map Agda=weakly-constant-map}},
or **steady**, if any two elements in `A` are mapped to
[identical elements](foundation-core.identity-types.md) in `B`. This concept is
considered in {{#cite KECA17}} where it is in particular used to give a
generalization of [Hedberg's theorem](foundation.decidable-equality.md).

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

  is-weakly-constant-map-weakly-constant-map :
    is-weakly-constant-map map-weakly-constant-map
  is-weakly-constant-map-weakly-constant-map = pr2 f
```

### Factorizations through propositions

```agda
factorization-through-Prop :
  {l1 l2 : Level} (l3 : Level) {A : UU l1} {B : UU l2} →
  (A → B) → UU (l1 ⊔ l2 ⊔ lsuc l3)
factorization-through-Prop l3 {A} {B} f =
  Σ ( Prop l3)
    ( λ P → Σ (type-Prop P → B) (λ i → Σ (A → type-Prop P) (λ j → i ∘ j ~ f)))
```

**Comment.** We need this type to state a factorization property of weakly
constant maps, but placing it in its appropriate place
(`orthogonal-factorization-systems.factorizations-of-maps`) leads to circular
dependencies.

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

  prop-fixed-point-is-weakly-constant-map : Prop l
  prop-fixed-point-is-weakly-constant-map =
    ( fixed-point f , is-prop-fixed-point-is-weakly-constant-map)
```

### The action on identifications of weakly constant maps is weakly constant

This is Auxiliary Lemma 4.3 of {{#cite KECA17}}.

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : X → Y}
  (W : is-weakly-constant-map f)
  where

  compute-ap-is-weakly-constant-map :
    {x y : X} (p : x ＝ y) → inv (W x x) ∙ W x y ＝ ap f p
  compute-ap-is-weakly-constant-map {x} refl = left-inv (W x x)

  is-weakly-constant-map-ap : {x y : X} → is-weakly-constant-map (ap f {x} {y})
  is-weakly-constant-map-ap {x} {y} p q =
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
      is-weakly-constant-map-ap (is-weakly-constant-map-weakly-constant-map f))
```

### Weakly constant maps are closed under composition with arbitrary maps

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  is-weakly-constant-map-right-comp :
    {f : A → B} (g : B → C) →
    is-weakly-constant-map f → is-weakly-constant-map (g ∘ f)
  is-weakly-constant-map-right-comp g W x y = ap g (W x y)

  is-weakly-constant-map-left-comp :
    (f : A → B) {g : B → C} →
    is-weakly-constant-map g → is-weakly-constant-map (g ∘ f)
  is-weakly-constant-map-left-comp f W x y = W (f x) (f y)
```

### A map is weakly constant if and only if it factors through a proposition

A map `f : A → B` is weakly constant if and only if there exists a proposition
`P` and a commuting diagram

```text
        P
      ∧   \
     /     \
    /       ∨
  A --------> B
        f
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  is-weakly-constant-map-factors-through-Prop :
    {l3 : Level} → factorization-through-Prop l3 f → is-weakly-constant-map f
  is-weakly-constant-map-factors-through-Prop (P , i , j , H) x y =
    inv (H x) ∙ ap i (eq-type-Prop P) ∙ H y
```

> The converse remains to be formalized.

## References

{{#bibliography}} {{#reference KECA17}}

## See also

- [Coherently constant maps](foundation.coherently-constant-maps.md)
- [Null-homotopic maps](foundation.null-homotopic-maps.md)

## External links

- [weakly constant function](https://ncatlab.org/nlab/show/weakly+constant+function)
  at $n$Lab
