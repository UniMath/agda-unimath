# Initial segments of ordinals

```agda
module order-theory.initial-segments-ordinals where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.booleans
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.similarity-subtypes
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import order-theory.accessible-elements-relations
open import order-theory.ordinals
open import order-theory.transitive-well-founded-relations
open import order-theory.well-founded-relations
```

</details>

## Idea

An
{{#concept "initial segment" Disambiguation="of an ordinal" Agda=initial-segment-Ordinal}}
of an [ordinal](order-theory.ordinals.md) `α` is a
[subtype](foundation-core.subtypes.md) `P : α → Prop` such that

```text
  x < y → P y → P x
```

holds for all `x` and `y` in `α`.

## Definitions

### The predicate on subtypes of ordinals of being initial segments

```agda
module _
  {l1 l2 l3 : Level}
  (α : Ordinal l1 l2)
  (let _<_ = le-Ordinal α)
  (P : subtype l3 (type-Ordinal α))
  where

  is-initial-segment-subtype-Ordinal :
    UU (l1 ⊔ l2 ⊔ l3)
  is-initial-segment-subtype-Ordinal =
    (x y : type-Ordinal α) → x < y → is-in-subtype P y → is-in-subtype P x

  is-prop-is-initial-segment-subtype-Ordinal :
    is-prop is-initial-segment-subtype-Ordinal
  is-prop-is-initial-segment-subtype-Ordinal =
    is-prop-Π
      ( λ x →
        is-prop-Π
          ( λ y →
            is-prop-function-type
              ( is-prop-function-type (is-prop-is-in-subtype P x))))

  is-initial-segment-subtype-prop-Ordinal : Prop (l1 ⊔ l2 ⊔ l3)
  is-initial-segment-subtype-prop-Ordinal =
    ( is-initial-segment-subtype-Ordinal ,
      is-prop-is-initial-segment-subtype-Ordinal)
```

### The type of initial segments of an ordinal

```agda
module _
  {l1 l2 : Level} (l3 : Level)
  (α : Ordinal l1 l2)
  (let _<_ = le-Ordinal α)
  where

  initial-segment-Ordinal : UU (l1 ⊔ l2 ⊔ lsuc l3)
  initial-segment-Ordinal =
    Σ ( subtype l3 (type-Ordinal α))
      ( is-initial-segment-subtype-Ordinal α)

module _
  {l1 l2 l3 : Level}
  (α : Ordinal l1 l2)
  (I : initial-segment-Ordinal l3 α)
  where

  subtype-initial-segment-Ordinal : subtype l3 (type-Ordinal α)
  subtype-initial-segment-Ordinal = pr1 I

  is-initial-segment-initial-segment-Ordinal :
    is-initial-segment-subtype-Ordinal α
      subtype-initial-segment-Ordinal
  is-initial-segment-initial-segment-Ordinal = pr2 I

  is-in-initial-segment-Ordinal : type-Ordinal α → UU l3
  is-in-initial-segment-Ordinal =
    is-in-subtype subtype-initial-segment-Ordinal

  is-closed-under-eq-initial-segment-Ordinal :
    {x y : type-Ordinal α} →
    is-in-initial-segment-Ordinal x →
    x ＝ y →
    is-in-initial-segment-Ordinal y
  is-closed-under-eq-initial-segment-Ordinal =
    is-closed-under-eq-subtype subtype-initial-segment-Ordinal

  is-closed-under-eq-initial-segment-Ordinal' :
    {x y : type-Ordinal α} →
    is-in-initial-segment-Ordinal y →
    x ＝ y →
    is-in-initial-segment-Ordinal x
  is-closed-under-eq-initial-segment-Ordinal' =
    is-closed-under-eq-subtype' subtype-initial-segment-Ordinal

module _
  {l1 l2 l3 : Level}
  (α : Ordinal l1 l2)
  where

  is-emb-subtype-initial-segment-Ordinal :
    is-emb (subtype-initial-segment-Ordinal {l3 = l3} α)
  is-emb-subtype-initial-segment-Ordinal =
    is-emb-inclusion-subtype (is-initial-segment-subtype-prop-Ordinal α)

  emb-subtype-initial-segment-Ordinal :
    initial-segment-Ordinal l3 α ↪ subtype l3 (type-Ordinal α)
  emb-subtype-initial-segment-Ordinal =
    (subtype-initial-segment-Ordinal α , is-emb-subtype-initial-segment-Ordinal)
```

### Initial segments with the same elements

```agda
module _
  {l1 l2 : Level} (α : Ordinal l1 l2)
  where

  has-same-elements-initial-segment-Ordinal :
    {l3 l4 : Level}
    (I : initial-segment-Ordinal l3 α)
    (J : initial-segment-Ordinal l4 α) →
    UU (l1 ⊔ l3 ⊔ l4)
  has-same-elements-initial-segment-Ordinal I J =
    has-same-elements-subtype
      ( subtype-initial-segment-Ordinal α I)
      ( subtype-initial-segment-Ordinal α J)

  extensionality-has-same-elements-initial-segment-Ordinal :
    {l3 : Level} (I J : initial-segment-Ordinal l3 α) →
    (I ＝ J) ≃ has-same-elements-initial-segment-Ordinal I J
  extensionality-has-same-elements-initial-segment-Ordinal I J =
    ( extensionality-subtype
      ( subtype-initial-segment-Ordinal α I)
      ( subtype-initial-segment-Ordinal α J)) ∘e
    ( equiv-ap-emb (emb-subtype-initial-segment-Ordinal α))
```

### Similarity of initial segments

```agda
module _
  {l1 l2 : Level} (α : Ordinal l1 l2)
  where

  sim-initial-segment-Ordinal :
    {l3 l4 : Level}
    (I : initial-segment-Ordinal l3 α)
    (J : initial-segment-Ordinal l4 α) →
    UU (l1 ⊔ l3 ⊔ l4)
  sim-initial-segment-Ordinal I J =
    sim-subtype
      ( subtype-initial-segment-Ordinal α I)
      ( subtype-initial-segment-Ordinal α J)

  extensionality-sim-initial-segment-Ordinal :
    {l3 : Level} (I J : initial-segment-Ordinal l3 α) →
    (I ＝ J) ≃ sim-initial-segment-Ordinal I J
  extensionality-sim-initial-segment-Ordinal I J =
    ( extensionality-sim-subtype
      ( subtype-initial-segment-Ordinal α I)
      ( subtype-initial-segment-Ordinal α J)) ∘e
    ( equiv-ap-emb (emb-subtype-initial-segment-Ordinal α))
```

## Properties

### The canonical inclusion of the ordinal into its type of initial segments

```agda
module _
  {l1 l2 : Level}
  (α : Ordinal l1 l2)
  (let _<_ = le-Ordinal α)
  where

  inclusion-initial-segment-Ordinal :
    type-Ordinal α → initial-segment-Ordinal l2 α
  inclusion-initial-segment-Ordinal x =
    ( ( λ u → le-prop-Ordinal α u x) ,
      ( λ y u y<u u<x → transitive-le-Ordinal α y u x u<x y<u))
```

### The well-founded relation on the type of initial segments

```agda
module _
  {l1 l2 : Level}
  (α : Ordinal l1 l2)
  (let _<_ = le-Ordinal α)
  where

  le-initial-segment-Ordinal :
    {l3 l4 : Level} →
    initial-segment-Ordinal l3 α →
    initial-segment-Ordinal l4 α →
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  le-initial-segment-Ordinal I J =
    Σ (type-Ordinal α)
      ( λ v →
        ( has-same-elements-initial-segment-Ordinal α I
          ( inclusion-initial-segment-Ordinal α v)) ×
        ( is-in-initial-segment-Ordinal α J v))

  transitive-le-initial-segment-Ordinal :
    {l3 l4 l5 : Level} →
    (I : initial-segment-Ordinal l3 α) →
    (J : initial-segment-Ordinal l4 α) →
    (K : initial-segment-Ordinal l5 α) →
    le-initial-segment-Ordinal J K →
    le-initial-segment-Ordinal I J →
    le-initial-segment-Ordinal I K
  pr1 (transitive-le-initial-segment-Ordinal I J K J<K I<J) = pr1 I<J
  pr1 (pr2 (transitive-le-initial-segment-Ordinal I J K J<K I<J)) =
    pr1 (pr2 I<J)
  pr2 (pr2 (transitive-le-initial-segment-Ordinal I J K J<K I<J)) =
    pr2 K (pr1 (transitive-le-initial-segment-Ordinal I J K J<K I<J))
    (pr1 J<K)
    (pr1
     (pr1 (pr2 J<K)
      (pr1 (transitive-le-initial-segment-Ordinal I J K J<K I<J)))
     (pr2 (pr2 I<J)))
    (pr2 (pr2 J<K))

  has-same-elements-refl-inclusion-initial-segment-Ordinal :
    (x : type-Ordinal α) →
    has-same-elements-initial-segment-Ordinal α
      (inclusion-initial-segment-Ordinal α x)
      (inclusion-initial-segment-Ordinal α x)
  has-same-elements-refl-inclusion-initial-segment-Ordinal x =
    map-equiv
      ( extensionality-has-same-elements-initial-segment-Ordinal α
        ( inclusion-initial-segment-Ordinal α x)
        ( inclusion-initial-segment-Ordinal α x))
      ( refl)

  le-inclusion-initial-segment-Ordinal :
    {l3 : Level}
    (I : initial-segment-Ordinal l3 α)
    (x : type-Ordinal α) →
    is-in-initial-segment-Ordinal α I x →
    le-initial-segment-Ordinal
      ( inclusion-initial-segment-Ordinal α x)
      ( I)
  le-inclusion-initial-segment-Ordinal I x x∈I =
    ( x ,
      ( has-same-elements-refl-inclusion-initial-segment-Ordinal x ,
        x∈I))

  is-well-founded-le-initial-segment-Ordinal :
    is-well-founded-Relation (le-initial-segment-Ordinal {l2} {l2})
  is-accessible-inclusion-initial-segment-Ordinal :
    (x : type-Ordinal α) →
    is-accessible-element-Relation
      (le-initial-segment-Ordinal {l2} {l2})
      (inclusion-initial-segment-Ordinal α x)
  is-accessible-inclusion-initial-segment-Ordinal =
    ind-Ordinal α
      ( λ x →
        is-accessible-element-Relation
          (le-initial-segment-Ordinal {l2} {l2})
          (inclusion-initial-segment-Ordinal α x))
      ( λ {x} IH →
        access
          ( λ {J} J<x →
            tr
              ( is-accessible-element-Relation
                (le-initial-segment-Ordinal {l2} {l2}))
              ( inv
                ( map-inv-equiv
                  ( extensionality-has-same-elements-initial-segment-Ordinal α
                    J
                    (inclusion-initial-segment-Ordinal α (pr1 J<x)))
                  ( pr1 (pr2 J<x))))
              ( IH (pr2 (pr2 J<x)))))

  is-well-founded-le-initial-segment-Ordinal I =
    access
      ( λ {J} J<I →
        tr
          ( is-accessible-element-Relation
            (le-initial-segment-Ordinal {l2} {l2}))
          ( inv
            ( map-inv-equiv
              ( extensionality-has-same-elements-initial-segment-Ordinal α
                J
                (inclusion-initial-segment-Ordinal α (pr1 J<I)))
              ( pr1 (pr2 J<I))))
          ( is-accessible-inclusion-initial-segment-Ordinal (pr1 J<I)))

  transitive-well-founded-relation-initial-segment-Ordinal :
    Transitive-Well-Founded-Relation
      ( l1 ⊔ l2)
      ( initial-segment-Ordinal l2 α)
  transitive-well-founded-relation-initial-segment-Ordinal =
    ( le-initial-segment-Ordinal {l2} {l2} ,
      ( is-well-founded-le-initial-segment-Ordinal ,
        transitive-le-initial-segment-Ordinal))
```

### A forcing construction for boolean predicates on initial segments

```agda
module _
  {l1 l2 : Level}
  (α : Ordinal l1 l2)
  (P : initial-segment-Ordinal l2 α → bool)
  where

  is-in-force-initial-segment-Ordinal :
    type-Ordinal α → UU (l1 ⊔ l2)
  is-in-force-initial-segment-Ordinal x =
    (y : type-Ordinal α) →
    leq-Ordinal α y x →
    is-false (P (inclusion-initial-segment-Ordinal α y))

  is-prop-is-in-force-initial-segment-Ordinal :
    (x : type-Ordinal α) → is-prop (is-in-force-initial-segment-Ordinal x)
  is-prop-is-in-force-initial-segment-Ordinal x =
    is-prop-Π
      ( λ y →
        is-prop-function-type
          ( is-prop-is-false
            ( P (inclusion-initial-segment-Ordinal α y))))

  force-subtype-initial-segment-Ordinal :
    subtype (l1 ⊔ l2) (type-Ordinal α)
  force-subtype-initial-segment-Ordinal x =
    ( is-in-force-initial-segment-Ordinal x ,
      is-prop-is-in-force-initial-segment-Ordinal x)

  is-initial-segment-force-subtype-initial-segment-Ordinal :
    is-initial-segment-subtype-Ordinal α force-subtype-initial-segment-Ordinal
  is-initial-segment-force-subtype-initial-segment-Ordinal x y x<y Hy z z≤x =
    Hy z
      ( transitive-leq-Ordinal α z x y
        ( leq-le-Ordinal α x<y)
        ( z≤x))

  force-initial-segment-Ordinal :
    initial-segment-Ordinal (l1 ⊔ l2) α
  force-initial-segment-Ordinal =
    ( force-subtype-initial-segment-Ordinal ,
      is-initial-segment-force-subtype-initial-segment-Ordinal)

  is-in-force-initial-segment-Ordinal' :
    type-Ordinal α → UU (l1 ⊔ l2)
  is-in-force-initial-segment-Ordinal' =
    is-in-initial-segment-Ordinal α force-initial-segment-Ordinal

  is-false-ev-inclusion-is-in-force-initial-segment-Ordinal :
    (x : type-Ordinal α) →
    is-in-force-initial-segment-Ordinal' x →
    is-false (P (inclusion-initial-segment-Ordinal α x))
  is-false-ev-inclusion-is-in-force-initial-segment-Ordinal x H =
    H x (refl-leq-Ordinal α x)
```
