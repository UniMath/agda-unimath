# The reduced 1-bordism category

```agda
module univalent-combinatorics.reduced-1-bordism-category where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.functions
open import foundation.universe-levels

open import graph-theory.directed-graphs
open import graph-theory.walks-directed-graphs

open import univalent-combinatorics.finite-types
```

</details>

## Idea

The reduced `1`-bordism category is the category of 1-bordisms where cycles are ignored.

## Definition

### Objects in the reduced `1`-bordism category

```agda
object-Reduced-1-Bordism : UU (lsuc lzero)
object-Reduced-1-Bordism = 𝔽 lzero × 𝔽 lzero

positive-finite-type-object-Reduced-1-Bordism :
  object-Reduced-1-Bordism → 𝔽 lzero
positive-finite-type-object-Reduced-1-Bordism = pr1

positive-type-object-Reduced-1-Bordism :
  object-Reduced-1-Bordism → UU lzero
positive-type-object-Reduced-1-Bordism =
  type-𝔽 ∘ positive-finite-type-object-Reduced-1-Bordism

negative-finite-type-object-Reduced-1-Bordism :
  object-Reduced-1-Bordism → 𝔽 lzero
negative-finite-type-object-Reduced-1-Bordism = pr2

negative-type-object-Reduced-1-Bordism :
  object-Reduced-1-Bordism → UU lzero
negative-type-object-Reduced-1-Bordism =
  type-𝔽 ∘ negative-finite-type-object-Reduced-1-Bordism
```

### Morphisms in the reduced `1`-bordism category

```agda
hom-Reduced-1-Bordism :
  (X Y : object-Reduced-1-Bordism) → UU lzero
hom-Reduced-1-Bordism X Y =
  ( positive-type-object-Reduced-1-Bordism X +
    negative-type-object-Reduced-1-Bordism Y) ≃
  ( positive-type-object-Reduced-1-Bordism Y +
    negative-type-object-Reduced-1-Bordism X)
```

### Identity morphisms in the reduced `1`-bordism category

```agda
id-hom-Reduced-1-Bordism :
  (X : object-Reduced-1-Bordism) → hom-Reduced-1-Bordism X X
id-hom-Reduced-1-Bordism X = id-equiv
```

### Composition of morphisms in the reduced `1`-bordism category

Composition of morphisms `g : (B⁺, B⁻) → (C⁺ , C⁻)` and `f : (A⁺ , A⁻) → (B⁺, B⁻)` of reduced `1`-bordisms is defined via the sequence of equivalences

```text
  (A⁺ ⊔ C⁻) ⊔ B⁻ ≃ (A⁺ ⊔ B⁻) ⊔ C⁻ 
                 ≃ (B⁺ ⊔ A⁻) ⊔ C⁻
                 ≃ (B⁺ ⊔ C⁻) ⊔ A⁻
                 ≃ (C⁺ ⊔ B⁻) ⊔ A⁻
                 ≃ (C⁺ ⊔ A⁻) ⊔ B⁻
```

Call the composite equivalence `φ`. Then `φ` induces a directed graph on the nods `(A⁺ ⊔ C⁻) ⊔ ((C⁺ ⊔ A⁻) ⊔ B⁻)` with the edge relation defined by

```text
  e₁ x : edge (inl x) (φ (inl x))
  e₂ b : edge (inr (inr b)) (φ (inr b))
```

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} {Z : 𝔽 l3}
  (φ : (X + type-𝔽 Z) ≃ (Y + type-𝔽 Z))
  where

  node-equiv-left-equiv-coprod : UU (l1 ⊔ l2 ⊔ l3)
  node-equiv-left-equiv-coprod = X + (Y + type-𝔽 Z)

  data edge-equiv-left-equiv-coprod :
    (u v : node-equiv-left-equiv-coprod) → UU (l1 ⊔ l2 ⊔ l3)
    where
    edge-to-value-equiv-left-equiv-coprod :
      (x : X) →
      edge-equiv-left-equiv-coprod (inl x) (inr (map-equiv φ (inl x)))
    edge-right-summand-equiv-left-equiv-coprod :
      (z : type-𝔽 Z) →
      edge-equiv-left-equiv-coprod (inr (inr z)) (inr (map-equiv φ (inr z)))

  directed-graph-equiv-left-equiv-coprod :
    Directed-Graph (l1 ⊔ l2 ⊔ l3) (l1 ⊔ l2 ⊔ l3)
  pr1 directed-graph-equiv-left-equiv-coprod =
    node-equiv-left-equiv-coprod
  pr2 directed-graph-equiv-left-equiv-coprod =
    edge-equiv-left-equiv-coprod

  walk-equiv-left-equiv-coprod :
    (x y : node-equiv-left-equiv-coprod) → UU (l1 ⊔ l2 ⊔ l3)
  walk-equiv-left-equiv-coprod =
    walk-Directed-Graph directed-graph-equiv-left-equiv-coprod

  walk-across-equiv-left-equiv-coprod :
    (x : X) →
    Σ Y (λ y → edge-equiv-left-equiv-coprod (inl x) (inr (inl y)))
  walk-across-equiv-left-equiv-coprod x = ?
```

In this graph, there is for each `x : A⁺ ⊔ C⁻` a unique element `y : C⁺ ⊔ A⁻` equipped with a walk from `inl x` to `inl (inr y)`. This determines an equivalence `A⁺ ⊔ C⁻ ≃ C⁺ ⊔ A⁻` which we use to define the composite `g ∘ f`.

```agda
comp-hom-Reduced-1-Bordism :
  {X Y Z : object-Reduced-1-Bordism} →
  hom-Reduced-1-Bordism Y Z → hom-Reduced-1-Bordism X Y →
  hom-Reduced-1-Bordism X Z
comp-hom-Reduced-1-Bordism g f = {!!}
```
