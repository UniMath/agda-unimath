# The reduced 1-bordism category

```agda
module univalent-combinatorics.reduced-1-bordism-category where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.identity-types
open import foundation.transport
open import foundation.type-arithmetic-coproduct-types
open import foundation.universe-levels

open import graph-theory.directed-graphs
open import graph-theory.walks-directed-graphs

open import univalent-combinatorics.finite-types
```

</details>

## Idea

The reduced `1`-bordism category is the category of 1-bordisms where cycles are
ignored.

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

Composition of morphisms `g : (B⁺, B⁻) → (C⁺ , C⁻)` and
`f : (A⁺ , A⁻) → (B⁺, B⁻)` of reduced `1`-bordisms is defined via the sequence
of equivalences

```text
  (A⁺ ⊔ C⁻) ⊔ B⁻ ≃ (A⁺ ⊔ B⁻) ⊔ C⁻
                 ≃ (B⁺ ⊔ A⁻) ⊔ C⁻
                 ≃ (B⁺ ⊔ C⁻) ⊔ A⁻
                 ≃ (C⁺ ⊔ B⁻) ⊔ A⁻
                 ≃ (C⁺ ⊔ A⁻) ⊔ B⁻
```

Call the composite equivalence `φ`. Then `φ` induces a directed graph on the
nods `(A⁺ ⊔ C⁻) ⊔ ((C⁺ ⊔ A⁻) ⊔ B⁻)` with the edge relation defined by

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

  direct-successor-equiv-left-equiv-coprod :
    (x : X) →
    direct-successor-Directed-Graph
      ( directed-graph-equiv-left-equiv-coprod)
      ( inl x)
  pr1 (direct-successor-equiv-left-equiv-coprod x) = inr (map-equiv φ (inl x))
  pr2 (direct-successor-equiv-left-equiv-coprod x) =
    edge-to-value-equiv-left-equiv-coprod x

  contraction-direct-successor-equiv-left-equiv-coprod :
    (x : X)
    ( s :
      direct-successor-Directed-Graph
        ( directed-graph-equiv-left-equiv-coprod)
        ( inl x)) →
    direct-successor-equiv-left-equiv-coprod x ＝ s
  contraction-direct-successor-equiv-left-equiv-coprod x
    ( ._ , edge-to-value-equiv-left-equiv-coprod .x) =
    refl

  unique-direct-successor-equiv-left-equiv-coprod :
    (x : X) →
    is-contr
      ( direct-successor-Directed-Graph
        ( directed-graph-equiv-left-equiv-coprod)
        ( inl x))
  pr1 (unique-direct-successor-equiv-left-equiv-coprod x) =
    direct-successor-equiv-left-equiv-coprod x
  pr2 (unique-direct-successor-equiv-left-equiv-coprod x) =
    contraction-direct-successor-equiv-left-equiv-coprod x

  cases-direct-predecessor-equiv-left-equiv-coprod :
    (y : Y) →
    ( Σ X (λ x → map-equiv φ (inl x) ＝ inl y) +
      Σ (type-𝔽 Z) (λ z → map-equiv φ (inr z) ＝ inl y)) →
    direct-predecessor-Directed-Graph
      ( directed-graph-equiv-left-equiv-coprod)
      ( inr (inl y))
  pr1 (cases-direct-predecessor-equiv-left-equiv-coprod y (inl (x , p))) =
    inl x
  pr2 (cases-direct-predecessor-equiv-left-equiv-coprod y (inl (x , p))) =
    tr
      ( edge-equiv-left-equiv-coprod (inl x))
      ( ap inr p)
      ( edge-to-value-equiv-left-equiv-coprod x)
  pr1 (cases-direct-predecessor-equiv-left-equiv-coprod y (inr (z , p))) =
    inr (inr z)
  pr2 (cases-direct-predecessor-equiv-left-equiv-coprod y (inr (z , p))) =
    tr
      ( edge-equiv-left-equiv-coprod (inr (inr z)))
      ( ap inr p)
      ( edge-right-summand-equiv-left-equiv-coprod z)

  direct-predecessor-equiv-left-equiv-coprod :
    (y : Y) →
    direct-predecessor-Directed-Graph
      ( directed-graph-equiv-left-equiv-coprod)
      ( inr (inl y))
  direct-predecessor-equiv-left-equiv-coprod y =
    cases-direct-predecessor-equiv-left-equiv-coprod y
      ( map-right-distributive-Σ-coprod X
        ( type-𝔽 Z)
        ( λ u → map-equiv φ u ＝ inl y)
        ( center (is-contr-map-is-equiv (is-equiv-map-equiv φ) (inl y))))

  cases-contraction-direct-predecessor-equiv-left-equiv-coprod :
    ( y : Y) →
    ( d :
      Σ X (λ x → map-equiv φ (inl x) ＝ inl y) +
      Σ (type-𝔽 Z) (λ z → map-equiv φ (inr z) ＝ inl y))
    ( p :
      direct-predecessor-Directed-Graph
        ( directed-graph-equiv-left-equiv-coprod)
        ( inr (inl y))) →
    cases-direct-predecessor-equiv-left-equiv-coprod y d ＝ p
  cases-contraction-direct-predecessor-equiv-left-equiv-coprod y
    ( inl (x , q)) (inl x' , e) =
    {!!}
    {-
    ap
      ( pr1)
      ( ( eq-is-contr (is-contr-map-is-equiv (is-equiv-map-equiv φ) (inl y)))
        { inl x , q}
        { inl x' , ?}) -}
  cases-contraction-direct-predecessor-equiv-left-equiv-coprod y
    ( inl (x , q)) (inr n , e) =
    {!!}
  cases-contraction-direct-predecessor-equiv-left-equiv-coprod y
    ( inr (z , q)) p =
    {!!}

  unique-direct-predecessor-equiv-left-equiv-coprod :
    (y : Y) →
    is-contr
      ( direct-predecessor-Directed-Graph
        ( directed-graph-equiv-left-equiv-coprod)
        ( inr (inl y)))
  unique-direct-predecessor-equiv-left-equiv-coprod y = {!!}

  walk-equiv-left-equiv-coprod :
    (x y : node-equiv-left-equiv-coprod) → UU (l1 ⊔ l2 ⊔ l3)
  walk-equiv-left-equiv-coprod =
    walk-Directed-Graph directed-graph-equiv-left-equiv-coprod

  walk-across-equiv-left-equiv-coprod :
    (x : X) →
    Σ Y (λ y → edge-equiv-left-equiv-coprod (inl x) (inr (inl y)))
  walk-across-equiv-left-equiv-coprod x = {!!}
```

In this graph, there is for each `x : A⁺ ⊔ C⁻` a unique element `y : C⁺ ⊔ A⁻`
equipped with a walk from `inl x` to `inl (inr y)`. This determines an
equivalence `A⁺ ⊔ C⁻ ≃ C⁺ ⊔ A⁻` which we use to define the composite `g ∘ f`.

```agda
comp-hom-Reduced-1-Bordism :
  {X Y Z : object-Reduced-1-Bordism} →
  hom-Reduced-1-Bordism Y Z → hom-Reduced-1-Bordism X Y →
  hom-Reduced-1-Bordism X Z
comp-hom-Reduced-1-Bordism g f = {!!}
```
