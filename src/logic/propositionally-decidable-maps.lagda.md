# Propositionally decidable maps

```agda
module logic.propositionally-decidable-maps where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.coproduct-types
open import foundation.decidable-dependent-pair-types
open import foundation.decidable-maps
open import foundation.dependent-pair-types
open import foundation.double-negation-dense-equality-maps
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.universe-levels

open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.injective-maps
open import foundation-core.iterating-functions

open import logic.propositionally-decidable-types
```

</details>

## Idea

A [map](foundation-core.function-types.md) is said to be
{{#concept "propositionally decidable" Disambiguation="map of types" Agda=is-inhabited-or-empty-map}}
if its [fibers](foundation-core.fibers-of-maps.md) are
[propositionally decidable types](logic.propositionally-decidable-types.md),
i.e., if they are merely [inhabited](foundation.inhabited-types.md) or
[empty](foundation.empty-types.md).

## Definitions

### The propositional decidability predicate on a map

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-inhabited-or-empty-map : (A → B) → UU (l1 ⊔ l2)
  is-inhabited-or-empty-map f = (y : B) → is-inhabited-or-empty (fiber f y)
```

### The type of propositionally decidable maps

```agda
inhabited-or-empty-map : {l1 l2 : Level} (A : UU l1) (B : UU l2) → UU (l1 ⊔ l2)
inhabited-or-empty-map A B = Σ (A → B) (is-inhabited-or-empty-map)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : inhabited-or-empty-map A B)
  where

  map-inhabited-or-empty-map : A → B
  map-inhabited-or-empty-map = pr1 f

  is-inhabited-or-empty-inhabited-or-empty-map :
    is-inhabited-or-empty-map map-inhabited-or-empty-map
  is-inhabited-or-empty-inhabited-or-empty-map = pr2 f
```

## Properties

### Propositionally decidable maps are closed under homotopy

```agda
abstract
  is-inhabited-or-empty-map-htpy :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f g : A → B} →
    f ~ g → is-inhabited-or-empty-map g → is-inhabited-or-empty-map f
  is-inhabited-or-empty-map-htpy H K b =
    is-inhabited-or-empty-equiv
      ( equiv-tot (λ a → equiv-concat (inv (H a)) b))
      ( K b)
```

### Decidable maps are propositionally decidable

```agda
is-inhabited-or-empty-map-is-decidable-map :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-decidable-map f → is-inhabited-or-empty-map f
is-inhabited-or-empty-map-is-decidable-map H x =
  is-inhabited-or-empty-is-decidable (H x)
```

### The identity map is propositionally decidable

```agda
abstract
  is-inhabited-or-empty-map-id :
    {l : Level} {X : UU l} → is-inhabited-or-empty-map (id {l} {X})
  is-inhabited-or-empty-map-id y = inl (unit-trunc-Prop (y , refl))
```

### Composition of propositionally decidable maps

The composite `g ∘ f` of two propositionally decidable maps is propositionally
decidable if `g` is injective.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {g : B → C} {f : A → B}
  where

  abstract
    is-inhabited-or-empty-map-comp :
      is-injective g →
      is-inhabited-or-empty-map g →
      is-inhabited-or-empty-map f →
      is-inhabited-or-empty-map (g ∘ f)
    is-inhabited-or-empty-map-comp H G F x =
      is-inhabited-or-empty-equiv
        ( compute-fiber-comp g f x)
        ( elim-is-inhabited-or-empty-Prop
          ( is-inhabited-or-empty-Prop
            ( Σ (fiber g x) (fiber f ∘ pr1)))
          ( λ t →
            elim-is-inhabited-or-empty-Prop
              ( is-inhabited-or-empty-Prop (Σ (fiber g x) (fiber f ∘ pr1)))
              ( λ s → inl (unit-trunc-Prop (t , s)))
              ( λ ns →
                inr
                  ( λ ts →
                    ns
                      ( pr1 (pr2 ts) ,
                        pr2 (pr2 ts) ∙ H ((pr2 (pr1 ts)) ∙ inv (pr2 t)))))
              ( F (pr1 t)))
          ( λ nt → inr (λ ts → nt (pr1 ts)))
          ( G x))
```

The composite `g ∘ f` of two propositionally decidable maps is propositionally
decidable if `g` has double negation dense equality.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {g : B → C} {f : A → B}
  where

  abstract
    is-inhabited-or-empty-map-comp-has-double-negation-dense-equality-map :
      has-double-negation-dense-equality-map g →
      is-inhabited-or-empty-map g →
      is-inhabited-or-empty-map f →
      is-inhabited-or-empty-map (g ∘ f)
    is-inhabited-or-empty-map-comp-has-double-negation-dense-equality-map
      H G F x =
      is-inhabited-or-empty-equiv
        ( compute-fiber-comp g f x)
        ( is-inhabited-or-empty-Σ-has-double-negation-dense-equality-base
          ( H x)
          ( G x)
          ( F ∘ pr1))

module _
  {l1 : Level} {A : UU l1} {f : A → A}
  (is-inhabited-or-empty-f : is-inhabited-or-empty-map f)
  (F : has-double-negation-dense-equality-map f)
  where

  is-inhabited-or-empty-map-iterate-has-double-negation-dense-equality-map :
    (n : ℕ) → is-inhabited-or-empty-map (iterate n f)
  is-inhabited-or-empty-map-iterate-has-double-negation-dense-equality-map
    zero-ℕ =
    is-inhabited-or-empty-map-id
  is-inhabited-or-empty-map-iterate-has-double-negation-dense-equality-map
    ( succ-ℕ n) =
    is-inhabited-or-empty-map-comp-has-double-negation-dense-equality-map
      ( F)
      ( is-inhabited-or-empty-f)
      ( is-inhabited-or-empty-map-iterate-has-double-negation-dense-equality-map
        ( n))
```
