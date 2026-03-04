# Oracle sheaves

```agda
module logic.oracle-sheaves where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.diagonal-maps-of-types
open import foundation.equivalences
open import foundation.evaluation-functions
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.universe-levels

open import logic.oracle-modalities

open import orthogonal-factorization-systems.null-types
```

</details>

## Idea

Given an [oracle modality](logic.oracle-modalities.md) `𝒪ₚ`, then a
{{#concept "oracle sheaf" Disambiguation="type" Agda=is-oracle-sheaf Agda=oracle-sheaf}}
is a type `X` such that for every proposition `s` such that `𝒪ₚs` holds, then
`X` is `s`-[null](orthogonal-factorization-systems.null-types.md). I.e., the
diagonal map

```text
  X → (s → X)
```

is an [equivalence](foundation-core.equivalences.md).

## Definitions

### The predicate on a type of being an oracle sheaf

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} (p : A → Prop l2)
  (𝒪ₚ : oracle-modality l3 l4 l5 p)
  (X : UU l6)
  where

  is-oracle-sheaf :
    UU (lsuc l3 ⊔ l4 ⊔ l6)
  is-oracle-sheaf =
    (s : Prop l3) →
    type-oracle-modality p 𝒪ₚ (type-Prop s) →
    is-null (type-Prop s) X

  is-prop-is-oracle-sheaf :
    is-prop is-oracle-sheaf
  abstract
    is-prop-is-oracle-sheaf =
      is-prop-Π (λ s → is-prop-Π (λ _ → is-prop-is-null (type-Prop s) X))

  oracle-sheaf-Prop :
    Prop (lsuc l3 ⊔ l4 ⊔ l6)
  oracle-sheaf-Prop =
    ( is-oracle-sheaf , is-prop-is-oracle-sheaf)
```

### The type of oracle sheaves

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (l6 : Level)
  {A : UU l1} (p : A → Prop l2)
  (𝒪ₚ : oracle-modality l3 l4 l5 p)
  where

  oracle-sheaf :
    UU (lsuc l3 ⊔ l4 ⊔ lsuc l6)
  oracle-sheaf =
    Σ (UU l6) (is-oracle-sheaf p 𝒪ₚ)
```

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} (p : A → Prop l2)
  (𝒪ₚ : oracle-modality l3 l4 l5 p)
  (X : oracle-sheaf l6 p 𝒪ₚ)
  where

  type-oracle-sheaf : UU l6
  type-oracle-sheaf = pr1 X

  is-oracle-sheaf-type-oracle-sheaf :
    is-oracle-sheaf p 𝒪ₚ type-oracle-sheaf
  is-oracle-sheaf-type-oracle-sheaf = pr2 X
```

### Oracle sheaf structure

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} (p : A → Prop l2)
  (𝒪ₚ : oracle-modality l3 l4 l5 p)
  (X : UU l6)
  where

  has-structure-oracle-sheaf :
    UU (l1 ⊔ l2 ⊔ l6)
  has-structure-oracle-sheaf =
    Σ ((a : A) → (type-Prop (p a) → X) → X)
      ( λ d →
        ( (a : A) (h : type-Prop (p a) → X) (u : type-Prop (p a)) →
          d a h ＝ h u) ×
          ( (x y : X) (a : A) → (type-Prop (p a) → x ＝ y) → x ＝ y))
```

## Properties

### A type is an oracle sheaf if and only if it has an oracle sheaf structure

This is Theorem 4.2 in {{#cite AB26}}.

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} (p : A → Prop l2)
  (𝒪ₚ : oracle-modality l2 l3 (l2 ⊔ l4) p)
  (X : UU l4)
  where

  structure-map-is-oracle-sheaf :
    is-oracle-sheaf p 𝒪ₚ X → ((a : A) → (type-Prop (p a) → X) → X)
  structure-map-is-oracle-sheaf H a h =
    map-inv-is-equiv (H (p a) (is-dense-self-oracle-modality p 𝒪ₚ a)) h

  compute-map-has-structure-oracle-sheaf-is-oracle-sheaf :
    (H : is-oracle-sheaf p 𝒪ₚ X) →
    ( a : A) (h : type-Prop (p a) → X) (u : type-Prop (p a)) →
    structure-map-is-oracle-sheaf H a h ＝ h u
  compute-map-has-structure-oracle-sheaf-is-oracle-sheaf H a h u =
    ap
      ( ev u)
      ( is-section-map-inv-is-equiv
        ( H (p a) (is-dense-self-oracle-modality p 𝒪ₚ a))
        ( h))

  map-Id-has-structure-oracle-sheaf-is-oracle-sheaf :
    (H : is-oracle-sheaf p 𝒪ₚ X) →
    (x y : X) (a : A) → (type-Prop (p a) → x ＝ y) → x ＝ y
  map-Id-has-structure-oracle-sheaf-is-oracle-sheaf H x y a f =
    ( inv
      ( is-retraction-map-inv-is-equiv
        ( H (p a) (is-dense-self-oracle-modality p 𝒪ₚ a))
        ( x))) ∙
    ( ap
      ( map-inv-is-equiv
        ( H (p a) (is-dense-self-oracle-modality p 𝒪ₚ a)))
      ( eq-htpy f)) ∙
    ( is-retraction-map-inv-is-equiv
      ( H (p a) (is-dense-self-oracle-modality p 𝒪ₚ a))
      ( y))

  has-structure-oracle-sheaf-is-oracle-sheaf :
    is-oracle-sheaf p 𝒪ₚ X → has-structure-oracle-sheaf p 𝒪ₚ X
  has-structure-oracle-sheaf-is-oracle-sheaf H =
    ( structure-map-is-oracle-sheaf H ,
      compute-map-has-structure-oracle-sheaf-is-oracle-sheaf H ,
      map-Id-has-structure-oracle-sheaf-is-oracle-sheaf H)
```

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} (p : A → Prop l2)
  (𝒪ₚ : oracle-modality l2 l3 (l2 ⊔ l4) p)
  (X : UU l4)
  (S : has-structure-oracle-sheaf p 𝒪ₚ X)
  where

  map-has-structure-oracle-sheaf :
    (a : A) → (type-Prop (p a) → X) → X
  map-has-structure-oracle-sheaf = pr1 S

  compute-map-has-structure-oracle-sheaf :
    (a : A) (h : type-Prop (p a) → X) (u : type-Prop (p a)) →
    map-has-structure-oracle-sheaf a h ＝ h u
  compute-map-has-structure-oracle-sheaf = pr1 (pr2 S)

  map-Id-has-structure-oracle-sheaf :
    (x y : X) (a : A) → (type-Prop (p a) → x ＝ y) → x ＝ y
  map-Id-has-structure-oracle-sheaf = pr2 (pr2 S)

  is-null-ask-has-structure-oracle-sheaf :
    (s : Prop l2) →
    (a : A) →
    (f : type-Prop (p a) → type-oracle-modality p 𝒪ₚ (type-Prop s)) →
    (f* : type-Prop (p a) → is-null (type-Prop s) X) →
    is-null (type-Prop s) X
  is-null-ask-has-structure-oracle-sheaf s a _ f* =
    is-equiv-is-invertible
      {f = diagonal-exponential X (type-Prop s)}
      ( λ h →
        map-has-structure-oracle-sheaf a (λ u → map-inv-is-equiv (f* u) h))
      ( λ h →
        eq-htpy
          ( λ v →
            map-Id-has-structure-oracle-sheaf
              ( map-has-structure-oracle-sheaf a
                ( λ u → map-inv-is-equiv (f* u) h))
              ( h v)
              ( a)
              ( λ u →
                ( compute-map-has-structure-oracle-sheaf a
                  ( λ u' → map-inv-is-equiv (f* u') h)
                  ( u)) ∙
                ( ap (ev v) (is-section-map-inv-is-equiv (f* u) h)))))
      ( λ x →
        map-Id-has-structure-oracle-sheaf
          ( map-has-structure-oracle-sheaf a
            ( λ u → map-inv-is-equiv (f* u) (λ _ → x)))
          ( x)
          ( a)
          ( λ u →
            ( compute-map-has-structure-oracle-sheaf a
              ( λ u' → map-inv-is-equiv (f* u') (λ _ → x))
              ( u)) ∙
            ( is-retraction-map-inv-is-equiv (f* u) x)))

  is-oracle-sheaf-has-structure-oracle-sheaf :
    is-oracle-sheaf p 𝒪ₚ X
  is-oracle-sheaf-has-structure-oracle-sheaf s =
    rec-oracle-modality p 𝒪ₚ (type-Prop s)
      ( is-null-Prop (type-Prop s) X)
      ( λ u →
        is-null-is-contr-exponent
          X
          ( is-proof-irrelevant-type-Prop s u))
      ( is-null-ask-has-structure-oracle-sheaf s)
```

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} (p : A → Prop l2)
  (𝒪ₚ : oracle-modality l2 l3 (l2 ⊔ l4) p)
  (X : UU l4)
  where

  iff-has-structure-oracle-sheaf-is-oracle-sheaf :
    is-oracle-sheaf p 𝒪ₚ X ↔ has-structure-oracle-sheaf p 𝒪ₚ X
  iff-has-structure-oracle-sheaf-is-oracle-sheaf =
    ( has-structure-oracle-sheaf-is-oracle-sheaf p 𝒪ₚ X ,
      is-oracle-sheaf-has-structure-oracle-sheaf p 𝒪ₚ X)
```

### The oracle sheaf structure of oracle sheaves

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} (p : A → Prop l2)
  (𝒪ₚ : oracle-modality l2 l3 (l2 ⊔ l4) p)
  (X : oracle-sheaf l4 p 𝒪ₚ)
  where

  has-structure-oracle-sheaf-type-oracle-sheaf :
    has-structure-oracle-sheaf p 𝒪ₚ (type-oracle-sheaf p 𝒪ₚ X)
  has-structure-oracle-sheaf-type-oracle-sheaf =
    has-structure-oracle-sheaf-is-oracle-sheaf p 𝒪ₚ
      ( type-oracle-sheaf p 𝒪ₚ X)
      ( is-oracle-sheaf-type-oracle-sheaf p 𝒪ₚ X)

  structure-map-oracle-sheaf :
    (a : A) →
    (type-Prop (p a) → type-oracle-sheaf p 𝒪ₚ X) →
    type-oracle-sheaf p 𝒪ₚ X
  structure-map-oracle-sheaf =
    map-has-structure-oracle-sheaf p 𝒪ₚ
      ( type-oracle-sheaf p 𝒪ₚ X)
      ( has-structure-oracle-sheaf-type-oracle-sheaf)

  compute-structure-map-oracle-sheaf :
    ( a : A)
    (h : type-Prop (p a) → type-oracle-sheaf p 𝒪ₚ X)
    (u : type-Prop (p a)) →
    structure-map-oracle-sheaf a h ＝ h u
  compute-structure-map-oracle-sheaf =
    compute-map-has-structure-oracle-sheaf p 𝒪ₚ
      ( type-oracle-sheaf p 𝒪ₚ X)
      ( has-structure-oracle-sheaf-type-oracle-sheaf)

  structure-map-Id-oracle-sheaf :
    (x y : type-oracle-sheaf p 𝒪ₚ X) (a : A) →
    (type-Prop (p a) → x ＝ y) → x ＝ y
  structure-map-Id-oracle-sheaf =
    map-Id-has-structure-oracle-sheaf p 𝒪ₚ
      ( type-oracle-sheaf p 𝒪ₚ X)
      ( has-structure-oracle-sheaf-type-oracle-sheaf)
```

## References

{{#bibliography}}
