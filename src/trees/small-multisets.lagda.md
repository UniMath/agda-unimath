# Small multisets

```agda
module trees.small-multisets where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.small-types
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.univalence
open import foundation.universe-levels

open import trees.multisets
open import trees.w-types
```

</details>

## Idea

A [multiset](trees.multisets.md) `X := tree-𝕎 A α` is said to be
{{#concept "small" Disambiguation="multiset" Agda=is-small-𝕍}} with respect to a
[universe](foundation.universe-levels.md) `UU l` if its symbol `A` is a
[small type](foundation-core.small-types.md) with respect to `UU l`, and if
recursively each `α x` is a small multiset with respect to `UU l`.

## Definition

### Small multisets

```agda
is-small-𝕍-Prop : (l : Level) {l1 : Level} → 𝕍 l1 → Prop (l1 ⊔ lsuc l)
is-small-𝕍-Prop l (tree-𝕎 A α) =
  product-Prop (is-small-Prop l A) (Π-Prop A (λ x → is-small-𝕍-Prop l (α x)))

is-small-𝕍 : (l : Level) {l1 : Level} → 𝕍 l1 → UU (l1 ⊔ lsuc l)
is-small-𝕍 l X = type-Prop (is-small-𝕍-Prop l X)

is-prop-is-small-𝕍 : {l l1 : Level} (X : 𝕍 l1) → is-prop (is-small-𝕍 l X)
is-prop-is-small-𝕍 {l} X = is-prop-type-Prop (is-small-𝕍-Prop l X)
```

### Resizing small multisets

```agda
resize-𝕍 :
  {l1 l2 : Level} (X : 𝕍 l1) → is-small-𝕍 l2 X → 𝕍 l2
resize-𝕍 (tree-𝕎 A α) (pair (pair A' e) H2) =
  tree-𝕎 A'
    ( λ x' → resize-𝕍 (α (map-inv-equiv e x')) (H2 (map-inv-equiv e x')))
```

## Properties

### The comprehension of a small multiset equipped with a small predicate is small

```agda
is-small-comprehension-𝕍 :
  (l : Level) {l1 : Level} {X : 𝕍 l1} {P : shape-𝕎 X → UU l1} →
  is-small-𝕍 l X → ((x : shape-𝕎 X) → is-small l (P x)) →
  is-small-𝕍 l (comprehension-𝕍 X P)
is-small-comprehension-𝕍 l {l1} {tree-𝕎 A α} {P} (pair (pair X e) H) K =
  pair
    ( is-small-Σ (pair X e) K)
    ( λ t → H (pr1 t))
```

### The identity type between small multisets is small

```agda
is-small-eq-𝕍 :
  (l : Level) {l1 : Level} {X Y : 𝕍 l1} →
  is-small-𝕍 l X → is-small-𝕍 l Y → is-small l (X ＝ Y)
is-small-eq-𝕍 l
  {l1} {tree-𝕎 A α} {tree-𝕎 B β} (pair (pair X e) H) (pair (pair Y f) K) =
  is-small-equiv
    ( Eq-𝕎 (tree-𝕎 A α) (tree-𝕎 B β))
    ( equiv-Eq-𝕎-eq (tree-𝕎 A α) (tree-𝕎 B β))
    ( is-small-Σ
      ( is-small-equiv
        ( A ≃ B)
        ( equiv-univalence)
        ( pair
          ( X ≃ Y)
          ( equiv-precomp-equiv (inv-equiv e) Y ∘e equiv-postcomp-equiv f A)))
      ( σ))
  where
  σ : (x : A ＝ B) → is-small l ((z : A) → Eq-𝕎 (α z) (β (tr id x z)))
  σ refl =
    is-small-Π
      ( pair X e)
      ( λ x →
        is-small-equiv
          ( α x ＝ β x)
          ( inv-equiv (equiv-Eq-𝕎-eq (α x) (β x)))
          ( is-small-eq-𝕍 l (H x) (K x)))
```

### The elementhood relation between small multisets is small

```agda
is-small-∈-𝕍 :
  (l : Level) {l1 : Level} {X Y : 𝕍 l1} →
  is-small-𝕍 l X → is-small-𝕍 l Y → is-small l (X ∈-𝕍 Y)
is-small-∈-𝕍 l {l1} {tree-𝕎 A α} {tree-𝕎 B β} H (pair (pair Y f) K) =
  is-small-Σ
    ( pair Y f)
    ( λ b → is-small-eq-𝕍 l (K b) H)

is-small-∉-𝕍 :
  (l : Level) {l1 : Level} {X Y : 𝕍 l1} →
  is-small-𝕍 l X → is-small-𝕍 l Y → is-small l (X ∉-𝕍 Y)
is-small-∉-𝕍 l {l1} {X} {Y} H K =
  is-small-Π
    ( is-small-∈-𝕍 l {l1} {X} {Y} H K)
    ( λ x → Raise l empty)
```

### The resizing of a small multiset is small

```agda
is-small-resize-𝕍 :
  {l1 l2 : Level} (X : 𝕍 l1) (H : is-small-𝕍 l2 X) →
  is-small-𝕍 l1 (resize-𝕍 X H)
is-small-resize-𝕍 (tree-𝕎 A α) (pair (pair A' e) H2) =
  pair
    ( pair A (inv-equiv e))
    ( λ a' →
      is-small-resize-𝕍
        ( α (map-inv-equiv e a'))
        ( H2 (map-inv-equiv e a')))
```

### The type of `UU l2`-small multisets in `𝕍 l1` is equivalent to the type of `UU l1`-small multisets in `𝕍 l2`

```agda
resize-𝕍' :
  {l1 l2 : Level} →
  Σ (𝕍 l1) (is-small-𝕍 l2) → Σ (𝕍 l2) (is-small-𝕍 l1)
resize-𝕍' (pair X H) = pair (resize-𝕍 X H) (is-small-resize-𝕍 X H)

abstract
  resize-resize-𝕍 :
    {l1 l2 : Level} {x : 𝕍 l1} (H : is-small-𝕍 l2 x) →
    resize-𝕍 (resize-𝕍 x H) (is-small-resize-𝕍 x H) ＝ x
  resize-resize-𝕍 {x = tree-𝕎 A α} ((A' , e) , H) =
    eq-Eq-𝕎
      ( resize-𝕍
        ( resize-𝕍 (tree-𝕎 A α) ((A' , e) , H))
        ( is-small-resize-𝕍 (tree-𝕎 A α) ((A' , e) , H)))
      ( tree-𝕎 A α)
      ( pair
        ( refl)
        ( λ z →
          Eq-𝕎-eq
            ( resize-𝕍
              ( resize-𝕍
                ( α (map-inv-equiv e (map-equiv e z)))
                ( H (map-inv-equiv e (map-equiv e z))))
              ( is-small-resize-𝕍
                ( α (map-inv-equiv e (map-equiv e z)))
                ( H (map-inv-equiv e (map-equiv e z)))))
            ( α z)
            ( ( ap
                ( λ t →
                  resize-𝕍
                    ( resize-𝕍 (α t) (H t))
                    ( is-small-resize-𝕍 (α t) (H t)))
                ( is-retraction-map-inv-equiv e z)) ∙
              ( resize-resize-𝕍 (H z)))))

abstract
  resize-resize-𝕍' :
    {l1 l2 : Level} → (resize-𝕍' {l2} {l1} ∘ resize-𝕍' {l1} {l2}) ~ id
  resize-resize-𝕍' {l1} {l2} (pair X H) =
    eq-type-subtype
      ( is-small-𝕍-Prop l2)
      ( resize-resize-𝕍 H)

is-equiv-resize-𝕍' :
  {l1 l2 : Level} → is-equiv (resize-𝕍' {l1} {l2})
is-equiv-resize-𝕍' {l1} {l2} =
  is-equiv-is-invertible
    ( resize-𝕍' {l2} {l1})
    ( resize-resize-𝕍')
    ( resize-resize-𝕍')

equiv-resize-𝕍' :
  {l1 l2 : Level} → Σ (𝕍 l1) (is-small-𝕍 l2) ≃ Σ (𝕍 l2) (is-small-𝕍 l1)
equiv-resize-𝕍' {l1} {l2} = pair resize-𝕍' is-equiv-resize-𝕍'
```

The resizing operation on small multisets is an embedding

```agda
eq-resize-𝕍 :
  {l1 l2 : Level} {x y : 𝕍 l1} (H : is-small-𝕍 l2 x) (K : is-small-𝕍 l2 y) →
  (x ＝ y) ≃ (resize-𝕍 x H ＝ resize-𝕍 y K)
eq-resize-𝕍 {l1} {l2} H K =
  ( extensionality-type-subtype'
    ( is-small-𝕍-Prop l1)
    ( resize-𝕍' (pair _ H))
    ( resize-𝕍' (pair _ K))) ∘e
  ( ( equiv-ap (equiv-resize-𝕍') (pair _ H) (pair _ K)) ∘e
    ( inv-equiv
      ( extensionality-type-subtype'
        ( is-small-𝕍-Prop l2)
        ( pair _ H)
        ( pair _ K))))
```

### The resizing operation on small multisets respects the elementhood relation

```agda
abstract
  equiv-elementhood-resize-𝕍 :
    {l1 l2 : Level} {x y : 𝕍 l1} (H : is-small-𝕍 l2 x) (K : is-small-𝕍 l2 y) →
    (x ∈-𝕍 y) ≃ (resize-𝕍 x H ∈-𝕍 resize-𝕍 y K)
  equiv-elementhood-resize-𝕍 {x = X} {tree-𝕎 B β} H (pair (pair B' e) K) =
    equiv-Σ
      ( λ y' →
        ( component-𝕎 (resize-𝕍 (tree-𝕎 B β) (pair (pair B' e) K)) y') ＝
        ( resize-𝕍 X H))
      ( e)
      ( λ b →
        ( equiv-concat
          ( ap
            ( λ t → resize-𝕍 (β t) (K t))
            ( is-retraction-map-inv-equiv e b))
          ( resize-𝕍 X H)) ∘e
        ( eq-resize-𝕍 (K b) H))
```

### The type of all multisets of universe level `l1` is `UU l2`-small if each type in `UU l1` is `UU l2`-small

```agda
is-small-multiset-𝕍 :
  {l1 l2 : Level} →
  ((A : UU l1) → is-small l2 A) → (X : 𝕍 l1) → is-small-𝕍 l2 X
is-small-multiset-𝕍 {l1} {l2} H (tree-𝕎 A α) =
  pair (H A) (λ x → is-small-multiset-𝕍 H (α x))
```
