# Iterate-confluent maps

```agda
module foundation.iterate-confluent-maps where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.cartesian-product-types
open import foundation.cones-over-cospan-diagrams
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.equality-dependent-pair-types
open import foundation.function-extensionality
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.iterating-functions
open import foundation.pullbacks
open import foundation.standard-pullbacks
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.propositions
open import foundation-core.sets
```

</details>

## Idea

Given two [natural numbers](elementary-number-theory.natural-numbers.md) 𝑛 and
𝑚, an endomap `f : A → A` is
(𝑛,𝑚)-{{#concept "iterate-confluent" Disambiguation="endomap on type" Agda=is-iterate-confluent Agda=iterate-confluent-map}}
if there is a [homotopy](foundation-core.homotopies.md)

```text
  fⁿ ~ fᵐ.
```

## Definitions

### The structure on a map of (𝑛,𝑚)-iterate-confluence

```agda
is-iterate-confluent : {l : Level} {A : UU l} → ℕ → ℕ → (A → A) → UU l
is-iterate-confluent n m f = iterate n f ~ iterate m f
```

### The type of iterate-confluent maps on a type

```agda
iterate-confluent-map : {l : Level} → ℕ → ℕ → UU l → UU l
iterate-confluent-map n m A = Σ (A → A) (is-iterate-confluent n m)

module _
  {l : Level} {n m : ℕ} {A : UU l} (f : iterate-confluent-map n m A)
  where

  map-iterate-confluent-map : A → A
  map-iterate-confluent-map = pr1 f

  is-iterate-confluent-iterate-confluent-map :
    is-iterate-confluent n m map-iterate-confluent-map
  is-iterate-confluent-iterate-confluent-map = pr2 f
```

## Properties

### Being an iterate-confluent operation on a set is a property

```agda
module _
  {l : Level} (n m : ℕ) {A : UU l} (is-set-A : is-set A) (f : A → A)
  where

  is-prop-is-iterate-confluent-is-set : is-prop (is-iterate-confluent n m f)
  is-prop-is-iterate-confluent-is-set =
    is-prop-Π (λ x → is-set-A (iterate n f x) (iterate m f x))

  is-iterate-confluent-is-set-Prop : Prop l
  is-iterate-confluent-is-set-Prop =
    ( is-iterate-confluent n m f , is-prop-is-iterate-confluent-is-set)

module _
  {l : Level} (n m : ℕ) (A : Set l) (f : type-Set A → type-Set A)
  where

  is-prop-is-iterate-confluent-Set : is-prop (is-iterate-confluent n m f)
  is-prop-is-iterate-confluent-Set =
    is-prop-is-iterate-confluent-is-set n m (is-set-type-Set A) f

  is-iterate-confluent-prop-Set : Prop l
  is-iterate-confluent-prop-Set =
    ( is-iterate-confluent n m f , is-prop-is-iterate-confluent-Set)
```

### Iterate-confluence is preserved by homotopies

If a map `g` is homotopic to an iterate-confluent map `f`, then `g` is also
iterate-confluent.

```agda
module _
  {l : Level} (n m : ℕ) {A : UU l} {f g : A → A}
  (F : is-iterate-confluent n m f)
  where

  is-iterate-confluent-htpy : g ~ f → is-iterate-confluent n m g
  is-iterate-confluent-htpy H =
    htpy-iterate n H ∙h F ∙h inv-htpy (htpy-iterate m H)

  is-iterate-confluent-inv-htpy : f ~ g → is-iterate-confluent n m g
  is-iterate-confluent-inv-htpy H =
    inv-htpy (htpy-iterate n H) ∙h F ∙h htpy-iterate m H
```

### Pullback presentation of iterate-confluent maps

The type of (𝑛,𝑚)-iterate-confluent maps on a type `A` is the pullback

```text
     ∙ ------------> (A → A)
     | ⌟                |
     |                  |
     |                  | (iterate m , iterate n)
     |                  |
     ∨                  ∨
  (A → A) ----> (A → A) × (A → A).
            Δ
```

**Proof.** We have the commuting diagram

```text
  iterate-confluent-map A ------> Σ (f : A → A), (iterate n f ＝ iterate m f)
             |                                        |
             |                                        |
         gap |                                        |
             |                                        |
             ∨                                        ∨
     standard-pullback <-- Σ (f g : A → A), (iterate m f ＝ g) × (iterate n f ＝ g)
```

which factors `gap` as a composite of equivalences. ∎

```agda
module _
  {l : Level} (n m : ℕ) {A : UU l}
  where

  cone-iterate-confluent-map :
    cone {A = A → A} {A → A} {(A → A) × (A → A)}
      ( λ f → iterate m f , iterate n f)
      ( λ g → g , g)
      ( iterate-confluent-map n m A)
  cone-iterate-confluent-map =
    ( pr1 , iterate m ∘ pr1 , (λ h → eq-pair refl (eq-htpy (pr2 h))))

  compute-cogap-cone-iterate-confluent-map :
    gap
      ( λ f → iterate m f , iterate n f)
      ( λ g → g , g)
      ( cone-iterate-confluent-map) ~
    tot
      ( λ f → tot (λ g → eq-pair') ∘ (λ p → (iterate m f , refl , p)) ∘ eq-htpy)
  compute-cogap-cone-iterate-confluent-map h =
    eq-Eq-standard-pullback
      ( λ f → iterate m f , iterate n f)
      ( λ g → g , g)
      ( refl)
      ( refl)
      (inv right-unit)

  abstract
    is-pullback-cone-iterate-confluent-map :
      is-pullback
        ( λ f → iterate m f , iterate n f)
        ( λ g → g , g)
        ( cone-iterate-confluent-map)
    is-pullback-cone-iterate-confluent-map =
      is-equiv-htpy
        ( tot
          ( λ f →
            tot (λ g → eq-pair') ∘ (λ p → (iterate m f , refl , p)) ∘ eq-htpy))
        ( compute-cogap-cone-iterate-confluent-map)
        ( is-equiv-tot-is-fiberwise-equiv
          ( λ f →
            is-equiv-comp
              ( tot (λ g → eq-pair') ∘ (λ p → (iterate m f , refl , p)))
              ( eq-htpy)
              ( is-equiv-eq-htpy (iterate n f) (iterate m f))
              ( is-equiv-comp
                ( tot (λ g → eq-pair'))
                ( λ p → (iterate m f , refl , p))
                ( is-equiv-is-invertible
                  ( λ q → pr2 (pr2 q) ∙ inv (pr1 (pr2 q)))
                  ( λ where
                    (x , (refl , q)) →
                      eq-pair-eq-fiber (eq-pair-eq-fiber right-unit))
                  ( λ x → right-unit))
                ( is-equiv-tot-is-fiberwise-equiv
                  ( λ g →
                    is-equiv-eq-pair (iterate m f , iterate n f) (g , g))))))
```

## See also

- [Idempotent maps](foundation.idempotent-maps.md) are (2,1)-iterate-confluent
  maps.
