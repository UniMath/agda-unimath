# Initial segments of ordinals

```agda
module order-theory.initial-segments-ordinals where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.logical-equivalences
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
    ( subtype-initial-segment-Ordinal α ,
      is-emb-subtype-initial-segment-Ordinal)
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

  is-prop-has-same-elements-initial-segment-Ordinal :
    {l3 l4 : Level}
    (I : initial-segment-Ordinal l3 α)
    (J : initial-segment-Ordinal l4 α) →
    is-prop (has-same-elements-initial-segment-Ordinal I J)
  is-prop-has-same-elements-initial-segment-Ordinal I J =
    is-prop-has-same-elements-subtype
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

  le-at-initial-segment-Ordinal :
    {l3 l4 : Level} →
    initial-segment-Ordinal l3 α →
    initial-segment-Ordinal l4 α →
    type-Ordinal α →
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  le-at-initial-segment-Ordinal I J v =
    ( has-same-elements-initial-segment-Ordinal α I
      ( inclusion-initial-segment-Ordinal α v)) ×
    ( is-in-initial-segment-Ordinal α J v)

  is-prop-le-at-initial-segment-Ordinal :
    {l3 l4 : Level}
    (I : initial-segment-Ordinal l3 α)
    (J : initial-segment-Ordinal l4 α)
    (v : type-Ordinal α) →
    is-prop (le-at-initial-segment-Ordinal I J v)
  is-prop-le-at-initial-segment-Ordinal I J v =
    is-prop-product
      ( is-prop-has-same-elements-initial-segment-Ordinal α I
        ( inclusion-initial-segment-Ordinal α v))
      ( is-prop-is-in-subtype (subtype-initial-segment-Ordinal α J) v)

  le-initial-segment-Ordinal :
    {l3 l4 : Level} →
    initial-segment-Ordinal l3 α →
    initial-segment-Ordinal l4 α →
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  le-initial-segment-Ordinal I J =
    Σ (type-Ordinal α) (le-at-initial-segment-Ordinal I J)

  transitive-le-initial-segment-Ordinal :
    {l3 l4 l5 : Level} →
    (I : initial-segment-Ordinal l3 α) →
    (J : initial-segment-Ordinal l4 α) →
    (K : initial-segment-Ordinal l5 α) →
    le-initial-segment-Ordinal J K →
    le-initial-segment-Ordinal I J →
    le-initial-segment-Ordinal I K
  transitive-le-initial-segment-Ordinal
    I J K
    ( vJ<K , (same-elems-J<vJ<K , vJ<K∈K))
    ( vI<J , (same-elems-I<vI<J , vI<J∈J)) =
    ( vI<J ,
      same-elems-I<vI<J ,
      is-initial-segment-initial-segment-Ordinal α K vI<J vJ<K
        ( forward-implication (same-elems-J<vJ<K vI<J) vI<J∈J)
        ( vJ<K∈K))

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
    le-initial-segment-Ordinal (inclusion-initial-segment-Ordinal α x) I
  le-inclusion-initial-segment-Ordinal I x x∈I =
    ( x , has-same-elements-refl-inclusion-initial-segment-Ordinal x , x∈I)

  is-in-le-inclusion-initial-segment-Ordinal :
    {l3 : Level}
    (I : initial-segment-Ordinal l3 α)
    (x : type-Ordinal α) →
    le-initial-segment-Ordinal (inclusion-initial-segment-Ordinal α x) I →
    is-in-initial-segment-Ordinal α I x
  is-in-le-inclusion-initial-segment-Ordinal
    I x (v<x , (same-elems-<x-<v<x , v<x∈I)) =
    is-closed-under-eq-initial-segment-Ordinal' α I v<x∈I
      ( is-extensional-Ordinal α x v<x same-elems-<x-<v<x)

  eq-pr1-le-initial-segment-Ordinal :
    {l3 l4 : Level}
    (I : initial-segment-Ordinal l3 α)
    (J : initial-segment-Ordinal l4 α) →
    (p q : le-initial-segment-Ordinal I J) →
    pr1 p ＝ pr1 q
  eq-pr1-le-initial-segment-Ordinal
    I J
    ( v<p , (same-elems-I-<v<p , v<p∈J))
    ( v<q , (same-elems-I-<v<q , v<q∈J)) =
    is-extensional-Ordinal α v<p v<q
      ( λ u →
        ( ( λ u<v<p →
            forward-implication
              ( same-elems-I-<v<q u)
              ( backward-implication (same-elems-I-<v<p u) u<v<p)) ,
          ( λ u<v<q →
            forward-implication
              ( same-elems-I-<v<p u)
              ( backward-implication (same-elems-I-<v<q u) u<v<q))))

  is-prop-le-initial-segment-Ordinal :
    {l3 l4 : Level}
    (I : initial-segment-Ordinal l3 α)
    (J : initial-segment-Ordinal l4 α) →
    is-prop (le-initial-segment-Ordinal I J)
  is-prop-le-initial-segment-Ordinal I J =
    is-prop-all-elements-equal
      ( λ p q →
        eq-pair-Σ
          ( eq-pr1-le-initial-segment-Ordinal I J p q)
          ( eq-is-prop (is-prop-le-at-initial-segment-Ordinal I J (pr1 q))))

  le-prop-initial-segment-Ordinal :
    Relation-Prop (l1 ⊔ l2) (initial-segment-Ordinal l2 α)
  le-prop-initial-segment-Ordinal I J =
    ( le-initial-segment-Ordinal I J ,
      is-prop-le-initial-segment-Ordinal I J)

  is-well-founded-le-initial-segment-Ordinal :
    is-well-founded-Relation (le-initial-segment-Ordinal {l2} {l2})
  is-accessible-inclusion-initial-segment-Ordinal :
    (x : type-Ordinal α) →
    is-accessible-element-Relation
      ( le-initial-segment-Ordinal {l2} {l2})
      ( inclusion-initial-segment-Ordinal α x)
  is-accessible-inclusion-initial-segment-Ordinal =
    ind-Ordinal α
      ( λ x →
        is-accessible-element-Relation
          ( le-initial-segment-Ordinal {l2} {l2})
          ( inclusion-initial-segment-Ordinal α x))
      ( λ {x} IH →
        access
          ( λ {J} (vJ<x , same-elems-J-<vJ<x , vJ<x<x) →
            tr
              ( is-accessible-element-Relation
                ( le-initial-segment-Ordinal {l2} {l2}))
              ( inv
                ( map-inv-equiv
                  ( extensionality-has-same-elements-initial-segment-Ordinal α J
                    ( inclusion-initial-segment-Ordinal α vJ<x))
                  ( same-elems-J-<vJ<x)))
              ( IH vJ<x<x)))

  is-well-founded-le-initial-segment-Ordinal I =
    access
      ( λ {J} (vJ<I , same-elems-J-<vJ<I , _) →
        tr
          ( is-accessible-element-Relation
            ( le-initial-segment-Ordinal {l2} {l2}))
          ( inv
            ( map-inv-equiv
              ( extensionality-has-same-elements-initial-segment-Ordinal α J
                ( inclusion-initial-segment-Ordinal α vJ<I))
              ( same-elems-J-<vJ<I)))
          ( is-accessible-inclusion-initial-segment-Ordinal vJ<I))

  is-transitive-well-founded-relation-le-initial-segment-Ordinal :
    is-transitive-well-founded-relation-Relation
      ( le-initial-segment-Ordinal {l2} {l2})
  is-transitive-well-founded-relation-le-initial-segment-Ordinal =
    ( is-well-founded-le-initial-segment-Ordinal ,
      transitive-le-initial-segment-Ordinal)

  transitive-well-founded-relation-initial-segment-Ordinal :
    Transitive-Well-Founded-Relation
      ( l1 ⊔ l2)
      ( initial-segment-Ordinal l2 α)
  transitive-well-founded-relation-initial-segment-Ordinal =
    ( le-initial-segment-Ordinal {l2} {l2} ,
      is-transitive-well-founded-relation-le-initial-segment-Ordinal)

  extensionality-principle-le-prop-initial-segment-Ordinal :
    extensionality-principle-Ordinal le-prop-initial-segment-Ordinal
  extensionality-principle-le-prop-initial-segment-Ordinal I J H =
    map-inv-equiv
      ( extensionality-has-same-elements-initial-segment-Ordinal α I J)
      ( λ x →
        ( ( λ x∈I →
            is-in-le-inclusion-initial-segment-Ordinal J  x
              ( pr1
                ( H (inclusion-initial-segment-Ordinal α x))
                ( le-inclusion-initial-segment-Ordinal I x x∈I))) ,
          ( λ x∈J →
            is-in-le-inclusion-initial-segment-Ordinal I x
              ( pr2
                ( H (inclusion-initial-segment-Ordinal α x))
                ( le-inclusion-initial-segment-Ordinal J x x∈J)))))

  is-ordinal-le-prop-initial-segment-Ordinal :
    is-ordinal le-prop-initial-segment-Ordinal
  is-ordinal-le-prop-initial-segment-Ordinal =
    ( is-transitive-well-founded-relation-le-initial-segment-Ordinal ,
      extensionality-principle-le-prop-initial-segment-Ordinal)

  ordinal-initial-segment-Ordinal :
    Ordinal (l1 ⊔ lsuc l2) (l1 ⊔ l2)
  ordinal-initial-segment-Ordinal =
    ( initial-segment-Ordinal l2 α ,
      le-prop-initial-segment-Ordinal ,
      is-ordinal-le-prop-initial-segment-Ordinal)
```
