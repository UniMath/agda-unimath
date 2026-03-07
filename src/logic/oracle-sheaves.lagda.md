# Oracle sheaves

```agda
module logic.oracle-sheaves where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.diagonal-maps-of-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.evaluation-functions
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositional-extensionality
open import foundation.propositions
open import foundation.retracts-of-types
open import foundation.standard-pullbacks
open import foundation.transport-along-identifications
open import foundation.unit-type
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

  has-oracle-sheaf-structure :
    UU (l1 ⊔ l2 ⊔ l6)
  has-oracle-sheaf-structure =
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
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} (p : A → Prop l2)
  (𝒪ₚ : oracle-modality l2 l3 l4 p)
  (X : UU l5)
  where

  structure-map-is-oracle-sheaf :
    is-oracle-sheaf p 𝒪ₚ X → ((a : A) → (type-Prop (p a) → X) → X)
  structure-map-is-oracle-sheaf H a h =
    map-inv-is-equiv (H (p a) (is-dense-self-oracle-modality p 𝒪ₚ a)) h

  compute-map-has-oracle-sheaf-structure-is-oracle-sheaf :
    (H : is-oracle-sheaf p 𝒪ₚ X) →
    ( a : A) (h : type-Prop (p a) → X) (u : type-Prop (p a)) →
    structure-map-is-oracle-sheaf H a h ＝ h u
  compute-map-has-oracle-sheaf-structure-is-oracle-sheaf H a h u =
    ap
      ( ev u)
      ( is-section-map-inv-is-equiv
        ( H (p a) (is-dense-self-oracle-modality p 𝒪ₚ a))
        ( h))

  map-Id-has-oracle-sheaf-structure-is-oracle-sheaf :
    (H : is-oracle-sheaf p 𝒪ₚ X) →
    (x y : X) (a : A) → (type-Prop (p a) → x ＝ y) → x ＝ y
  map-Id-has-oracle-sheaf-structure-is-oracle-sheaf H x y a f =
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

  has-oracle-sheaf-structure-is-oracle-sheaf :
    is-oracle-sheaf p 𝒪ₚ X → has-oracle-sheaf-structure p 𝒪ₚ X
  has-oracle-sheaf-structure-is-oracle-sheaf H =
    ( structure-map-is-oracle-sheaf H ,
      compute-map-has-oracle-sheaf-structure-is-oracle-sheaf H ,
      map-Id-has-oracle-sheaf-structure-is-oracle-sheaf H)
```

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} (p : A → Prop l2)
  (𝒪ₚ : oracle-modality l2 l3 (l2 ⊔ l4) p)
  (X : UU l4)
  (S : has-oracle-sheaf-structure p 𝒪ₚ X)
  where

  map-has-oracle-sheaf-structure :
    (a : A) → (type-Prop (p a) → X) → X
  map-has-oracle-sheaf-structure = pr1 S

  compute-map-has-oracle-sheaf-structure :
    (a : A) (h : type-Prop (p a) → X) (u : type-Prop (p a)) →
    map-has-oracle-sheaf-structure a h ＝ h u
  compute-map-has-oracle-sheaf-structure = pr1 (pr2 S)

  map-Id-has-oracle-sheaf-structure :
    (x y : X) (a : A) → (type-Prop (p a) → x ＝ y) → x ＝ y
  map-Id-has-oracle-sheaf-structure = pr2 (pr2 S)

  is-null-ask-has-oracle-sheaf-structure :
    (s : Prop l2) →
    (a : A) →
    (f : type-Prop (p a) → type-oracle-modality p 𝒪ₚ (type-Prop s)) →
    (f* : type-Prop (p a) → is-null (type-Prop s) X) →
    is-null (type-Prop s) X
  is-null-ask-has-oracle-sheaf-structure s a _ f* =
    is-equiv-is-invertible
      {f = diagonal-exponential X (type-Prop s)}
      ( λ h →
        map-has-oracle-sheaf-structure a (λ u → map-inv-is-equiv (f* u) h))
      ( λ h →
        eq-htpy
          ( λ v →
            map-Id-has-oracle-sheaf-structure
              ( map-has-oracle-sheaf-structure a
                ( λ u → map-inv-is-equiv (f* u) h))
              ( h v)
              ( a)
              ( λ u →
                ( compute-map-has-oracle-sheaf-structure a
                  ( λ u' → map-inv-is-equiv (f* u') h)
                  ( u)) ∙
                ( ap (ev v) (is-section-map-inv-is-equiv (f* u) h)))))
      ( λ x →
        map-Id-has-oracle-sheaf-structure
          ( map-has-oracle-sheaf-structure a
            ( λ u → map-inv-is-equiv (f* u) (λ _ → x)))
          ( x)
          ( a)
          ( λ u →
            ( compute-map-has-oracle-sheaf-structure a
              ( λ u' → map-inv-is-equiv (f* u') (λ _ → x))
              ( u)) ∙
            ( is-retraction-map-inv-is-equiv (f* u) x)))

  is-oracle-sheaf-has-oracle-sheaf-structure :
    is-oracle-sheaf p 𝒪ₚ X
  is-oracle-sheaf-has-oracle-sheaf-structure s =
    rec-oracle-modality p 𝒪ₚ
      ( type-Prop s)
      ( is-null-Prop (type-Prop s) X)
      ( λ u →
        is-null-is-contr-exponent X (is-proof-irrelevant-type-Prop s u))
      ( is-null-ask-has-oracle-sheaf-structure s)
```

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} (p : A → Prop l2)
  (𝒪ₚ : oracle-modality l2 l3 (l2 ⊔ l4) p)
  (X : UU l4)
  where

  iff-has-oracle-sheaf-structure-is-oracle-sheaf :
    is-oracle-sheaf p 𝒪ₚ X ↔ has-oracle-sheaf-structure p 𝒪ₚ X
  iff-has-oracle-sheaf-structure-is-oracle-sheaf =
    ( has-oracle-sheaf-structure-is-oracle-sheaf p 𝒪ₚ X ,
      is-oracle-sheaf-has-oracle-sheaf-structure p 𝒪ₚ X)
```

### The oracle sheaf structure of oracle sheaves

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} (p : A → Prop l2)
  (𝒪ₚ : oracle-modality l2 l3 (l2 ⊔ l4) p)
  (X : oracle-sheaf l4 p 𝒪ₚ)
  where

  has-oracle-sheaf-structure-type-oracle-sheaf :
    has-oracle-sheaf-structure p 𝒪ₚ (type-oracle-sheaf p 𝒪ₚ X)
  has-oracle-sheaf-structure-type-oracle-sheaf =
    has-oracle-sheaf-structure-is-oracle-sheaf p 𝒪ₚ
      ( type-oracle-sheaf p 𝒪ₚ X)
      ( is-oracle-sheaf-type-oracle-sheaf p 𝒪ₚ X)

  structure-map-oracle-sheaf :
    (a : A) →
    (type-Prop (p a) → type-oracle-sheaf p 𝒪ₚ X) →
    type-oracle-sheaf p 𝒪ₚ X
  structure-map-oracle-sheaf =
    map-has-oracle-sheaf-structure p 𝒪ₚ
      ( type-oracle-sheaf p 𝒪ₚ X)
      ( has-oracle-sheaf-structure-type-oracle-sheaf)

  compute-structure-map-oracle-sheaf :
    ( a : A)
    (h : type-Prop (p a) → type-oracle-sheaf p 𝒪ₚ X)
    (u : type-Prop (p a)) →
    structure-map-oracle-sheaf a h ＝ h u
  compute-structure-map-oracle-sheaf =
    compute-map-has-oracle-sheaf-structure p 𝒪ₚ
      ( type-oracle-sheaf p 𝒪ₚ X)
      ( has-oracle-sheaf-structure-type-oracle-sheaf)

  structure-map-Id-oracle-sheaf :
    (x y : type-oracle-sheaf p 𝒪ₚ X) (a : A) →
    (type-Prop (p a) → x ＝ y) → x ＝ y
  structure-map-Id-oracle-sheaf =
    map-Id-has-oracle-sheaf-structure p 𝒪ₚ
      ( type-oracle-sheaf p 𝒪ₚ X)
      ( has-oracle-sheaf-structure-type-oracle-sheaf)
```

### Maps between oracle sheaves preserve structure maps

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} (p : A → Prop l2)
  (𝒪ₚ : oracle-modality l2 l3 (l2 ⊔ l4) p)
  (X Y : oracle-sheaf l4 p 𝒪ₚ)
  where

  preserves-structure-map-map-oracle-sheaf :
    (f : type-oracle-sheaf p 𝒪ₚ X → type-oracle-sheaf p 𝒪ₚ Y) →
    (a : A) →
    (h : type-Prop (p a) → type-oracle-sheaf p 𝒪ₚ X) →
    f (structure-map-oracle-sheaf p 𝒪ₚ X a h) ＝
    structure-map-oracle-sheaf p 𝒪ₚ Y a (f ∘ h)
  preserves-structure-map-map-oracle-sheaf f a h =
    structure-map-Id-oracle-sheaf p 𝒪ₚ Y
      ( f (structure-map-oracle-sheaf p 𝒪ₚ X a h))
      ( structure-map-oracle-sheaf p 𝒪ₚ Y a (f ∘ h))
      ( a)
      ( λ u →
        ( ap f (compute-structure-map-oracle-sheaf p 𝒪ₚ X a h u)) ∙
        ( inv (compute-structure-map-oracle-sheaf p 𝒪ₚ Y a (f ∘ h) u)))
```

### Oracle sheaves are closed under equivalences

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 : Level}
  {A : UU l1} (p : A → Prop l2)
  (𝒪ₚ : oracle-modality l3 l4 l5 p)
  {X : UU l6} {Y : UU l7}
  where

  is-oracle-sheaf-equiv :
    X ≃ Y → is-oracle-sheaf p 𝒪ₚ Y → is-oracle-sheaf p 𝒪ₚ X
  is-oracle-sheaf-equiv e H s t =
    is-null-equiv-base e (H s t)
```

### Oracle sheaves are closed under retracts

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 : Level}
  {A : UU l1} (p : A → Prop l2)
  (𝒪ₚ : oracle-modality l3 l4 l5 p)
  {X : UU l6} {Y : UU l7}
  where

  is-oracle-sheaf-retract :
    X retract-of Y →
    is-oracle-sheaf p 𝒪ₚ Y →
    is-oracle-sheaf p 𝒪ₚ X
  is-oracle-sheaf-retract e H s t =
    is-null-retract-base e (H s t)
```

### Oracle sheaves are closed under dependent products

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 : Level}
  {A : UU l1} (p : A → Prop l2)
  (𝒪ₚ : oracle-modality l3 l4 l5 p)
  {I : UU l6} {X : I → UU l7}
  where

  is-oracle-sheaf-Π :
    ((i : I) → is-oracle-sheaf p 𝒪ₚ (X i)) →
    is-oracle-sheaf p 𝒪ₚ ((i : I) → X i)
  is-oracle-sheaf-Π H s t =
    is-null-Π (λ i → H i s t)
```

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 : Level}
  {A : UU l1} (p : A → Prop l2)
  (𝒪ₚ : oracle-modality l3 l4 l5 p)
  {I : UU l6}
  (X : I → oracle-sheaf l7 p 𝒪ₚ)
  where

  is-oracle-sheaf-Π-type-oracle-sheaf :
    is-oracle-sheaf p 𝒪ₚ ((i : I) → type-oracle-sheaf p 𝒪ₚ (X i))
  is-oracle-sheaf-Π-type-oracle-sheaf =
    is-oracle-sheaf-Π p 𝒪ₚ
      ( λ i → is-oracle-sheaf-type-oracle-sheaf p 𝒪ₚ (X i))

  oracle-sheaf-Π : oracle-sheaf (l6 ⊔ l7) p 𝒪ₚ
  oracle-sheaf-Π =
    ( ((i : I) → type-oracle-sheaf p 𝒪ₚ (X i)) ,
      is-oracle-sheaf-Π-type-oracle-sheaf)
```

### Oracle sheaves are closed under dependent sums

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 : Level}
  {A : UU l1} (p : A → Prop l2)
  (𝒪ₚ : oracle-modality l3 l4 l5 p)
  (X : UU l6)
  (Y : X → UU l7)
  where

  is-oracle-sheaf-Σ :
    is-oracle-sheaf p 𝒪ₚ X →
    ((x : X) → is-oracle-sheaf p 𝒪ₚ (Y x)) →
    is-oracle-sheaf p 𝒪ₚ (Σ X Y)
  is-oracle-sheaf-Σ H K s t =
    is-null-Σ (H s t) (λ x → K x s t)
```

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 : Level}
  {A : UU l1} (p : A → Prop l2)
  (𝒪ₚ : oracle-modality l3 l4 l5 p)
  (X : oracle-sheaf l6 p 𝒪ₚ)
  (Y : type-oracle-sheaf p 𝒪ₚ X → oracle-sheaf l7 p 𝒪ₚ)
  where

  is-oracle-sheaf-Σ-type-oracle-sheaf :
    is-oracle-sheaf p 𝒪ₚ
      ( Σ ( type-oracle-sheaf p 𝒪ₚ X)
          ( λ x → type-oracle-sheaf p 𝒪ₚ (Y x)))
  is-oracle-sheaf-Σ-type-oracle-sheaf =
    is-oracle-sheaf-Σ p 𝒪ₚ
      ( type-oracle-sheaf p 𝒪ₚ X)
      ( λ x → type-oracle-sheaf p 𝒪ₚ (Y x))
      ( is-oracle-sheaf-type-oracle-sheaf p 𝒪ₚ X)
      ( λ x → is-oracle-sheaf-type-oracle-sheaf p 𝒪ₚ (Y x))

  oracle-sheaf-Σ :
    oracle-sheaf (l6 ⊔ l7) p 𝒪ₚ
  oracle-sheaf-Σ =
    ( Σ ( type-oracle-sheaf p 𝒪ₚ X)
        ( λ x → type-oracle-sheaf p 𝒪ₚ (Y x)) ,
      is-oracle-sheaf-Σ-type-oracle-sheaf)
```

### Oracle sheaves are closed under identity types

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} (p : A → Prop l2)
  (𝒪ₚ : oracle-modality l3 l4 l5 p)
  {X : UU l6}
  where

  is-oracle-sheaf-Id :
    is-oracle-sheaf p 𝒪ₚ X →
    (x y : X) → is-oracle-sheaf p 𝒪ₚ (x ＝ y)
  is-oracle-sheaf-Id H x y s t = is-null-Id (H s t) x y
```

### Contractible types are oracle sheaves

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} (p : A → Prop l2)
  (𝒪ₚ : oracle-modality l3 l4 l5 p)
  {X : UU l6}
  where

  is-oracle-sheaf-is-contr :
    is-contr X → is-oracle-sheaf p 𝒪ₚ X
  is-oracle-sheaf-is-contr H s _ =
    is-null-is-contr (type-Prop s) H
```

### The unit type is an oracle sheaf

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} (p : A → Prop l2)
  (𝒪ₚ : oracle-modality l3 l4 l5 p)
  where

  is-oracle-sheaf-unit : is-oracle-sheaf p 𝒪ₚ unit
  is-oracle-sheaf-unit =
    is-oracle-sheaf-is-contr p 𝒪ₚ is-contr-unit

  unit-oracle-sheaf : oracle-sheaf lzero p 𝒪ₚ
  unit-oracle-sheaf = (unit , is-oracle-sheaf-unit)
```

### Oracle sheaves are closed under standard pullbacks

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  {A : UU l1} (p : A → Prop l2)
  (𝒪ₚ : oracle-modality l3 l4 l5 p)
  where

  is-oracle-sheaf-standard-pullback :
    {X : UU l6} {Y : UU l7} {Z : UU l8}
    (f : X → Z) (g : Y → Z) →
    is-oracle-sheaf p 𝒪ₚ X →
    is-oracle-sheaf p 𝒪ₚ Y →
    is-oracle-sheaf p 𝒪ₚ Z →
    is-oracle-sheaf p 𝒪ₚ (standard-pullback f g)
  is-oracle-sheaf-standard-pullback f g HX HY HZ s t =
    is-null-standard-pullback f g (HX s t) (HY s t) (HZ s t)

  standard-pullback-oracle-sheaf :
    (X : oracle-sheaf l6 p 𝒪ₚ)
    (Y : oracle-sheaf l7 p 𝒪ₚ)
    (Z : oracle-sheaf l8 p 𝒪ₚ)
    (f : type-oracle-sheaf p 𝒪ₚ X → type-oracle-sheaf p 𝒪ₚ Z)
    (g : type-oracle-sheaf p 𝒪ₚ Y → type-oracle-sheaf p 𝒪ₚ Z) →
    oracle-sheaf (l6 ⊔ l7 ⊔ l8) p 𝒪ₚ
  standard-pullback-oracle-sheaf X Y Z f g =
    ( standard-pullback f g ,
      is-oracle-sheaf-standard-pullback f g
        ( is-oracle-sheaf-type-oracle-sheaf p 𝒪ₚ X)
        ( is-oracle-sheaf-type-oracle-sheaf p 𝒪ₚ Y)
        ( is-oracle-sheaf-type-oracle-sheaf p 𝒪ₚ Z))
```

### Oracle sheaves are closed under fibers

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 : Level}
  {A : UU l1} (p : A → Prop l2)
  (𝒪ₚ : oracle-modality l3 l4 l5 p)
  {X : UU l6} {Y : UU l7}
  (f : X → Y) (y : Y)
  where

  is-oracle-sheaf-fiber :
    is-oracle-sheaf p 𝒪ₚ X →
    is-oracle-sheaf p 𝒪ₚ Y →
    is-oracle-sheaf p 𝒪ₚ (fiber f y)
  is-oracle-sheaf-fiber HX HY s t =
    is-null-fiber f y (HX s t) (HY s t)

  is-oracle-sheaf-fiber' :
    is-oracle-sheaf p 𝒪ₚ X →
    is-oracle-sheaf p 𝒪ₚ Y →
    is-oracle-sheaf p 𝒪ₚ (fiber' f y)
  is-oracle-sheaf-fiber' HX HY s t =
    is-null-fiber' f y (HX s t) (HY s t)
```

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 : Level}
  {A : UU l1} (p : A → Prop l2)
  (𝒪ₚ : oracle-modality l3 l4 l5 p)
  (X : oracle-sheaf l6 p 𝒪ₚ)
  (Y : oracle-sheaf l7 p 𝒪ₚ)
  (f : type-oracle-sheaf p 𝒪ₚ X → type-oracle-sheaf p 𝒪ₚ Y)
  (y : type-oracle-sheaf p 𝒪ₚ Y)
  where

  fiber-oracle-sheaf :
    oracle-sheaf (l6 ⊔ l7) p 𝒪ₚ
  fiber-oracle-sheaf =
    ( fiber f y ,
      is-oracle-sheaf-fiber p 𝒪ₚ f y
        ( is-oracle-sheaf-type-oracle-sheaf p 𝒪ₚ X)
        ( is-oracle-sheaf-type-oracle-sheaf p 𝒪ₚ Y))

  fiber-oracle-sheaf' :
    oracle-sheaf (l6 ⊔ l7) p 𝒪ₚ
  fiber-oracle-sheaf' =
    ( fiber' f y ,
      is-oracle-sheaf-fiber' p 𝒪ₚ f y
        ( is-oracle-sheaf-type-oracle-sheaf p 𝒪ₚ X)
        ( is-oracle-sheaf-type-oracle-sheaf p 𝒪ₚ Y))
```

### If `p a` implies `q a` for all `a`, then `p`-oracle sheaves are `q`-oracle sheaves

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 : Level}
  {A : UU l1}
  (p : A → Prop l2)
  (q : A → Prop l3)
  (f : (a : A) → type-Prop (p a) → type-Prop (q a))
  (𝒪ₚ : oracle-modality l3 l4 l5 p)
  (𝒪q : oracle-modality l3 l6 (l3 ⊔ l7) q)
  (X : UU l7)
  where

  is-oracle-dense-implication-oracle :
    (a : A) → type-oracle-modality p 𝒪ₚ (type-Prop (q a))
  is-oracle-dense-implication-oracle a =
    ask-oracle-modality p 𝒪ₚ (type-Prop (q a)) a
      ( unit-oracle-modality p 𝒪ₚ (type-Prop (q a)) ∘ f a)

  map-has-oracle-sheaf-structure-implication-oracle :
    is-oracle-sheaf p 𝒪ₚ X →
    (a : A) → (type-Prop (q a) → X) → X
  map-has-oracle-sheaf-structure-implication-oracle H a h =
    map-inv-is-equiv (H (q a) (is-oracle-dense-implication-oracle a)) h

  compute-map-has-oracle-sheaf-structure-implication-oracle :
    (H : is-oracle-sheaf p 𝒪ₚ X) →
    (a : A) →
    (h : type-Prop (q a) → X) →
    (u : type-Prop (q a)) →
    map-has-oracle-sheaf-structure-implication-oracle H a h ＝ h u
  compute-map-has-oracle-sheaf-structure-implication-oracle H a h u =
    ap
      (ev u)
      (is-section-map-inv-is-equiv
        ( H (q a) (is-oracle-dense-implication-oracle a))
        ( h))

  map-Id-has-oracle-sheaf-structure-implication-oracle :
    (H : is-oracle-sheaf p 𝒪ₚ X) →
    (x y : X) →
    (a : A) →
    (type-Prop (q a) → x ＝ y) →
    x ＝ y
  map-Id-has-oracle-sheaf-structure-implication-oracle H x y a g =
    ( inv
      ( is-retraction-map-inv-is-equiv
        ( H (q a) (is-oracle-dense-implication-oracle a))
        ( x))) ∙
    ( ap
      ( map-inv-is-equiv
        ( H (q a) (is-oracle-dense-implication-oracle a)))
      ( eq-htpy g)) ∙
    ( is-retraction-map-inv-is-equiv
      ( H (q a) (is-oracle-dense-implication-oracle a))
      ( y))

  has-oracle-sheaf-structure-implication-oracle :
    is-oracle-sheaf p 𝒪ₚ X →
    has-oracle-sheaf-structure q 𝒪q X
  has-oracle-sheaf-structure-implication-oracle H =
    ( map-has-oracle-sheaf-structure-implication-oracle H ,
      compute-map-has-oracle-sheaf-structure-implication-oracle H ,
      map-Id-has-oracle-sheaf-structure-implication-oracle H)

  is-oracle-sheaf-implication-oracle :
    is-oracle-sheaf p 𝒪ₚ X →
    is-oracle-sheaf q 𝒪q X
  is-oracle-sheaf-implication-oracle H =
    is-oracle-sheaf-has-oracle-sheaf-structure q 𝒪q X
      ( has-oracle-sheaf-structure-implication-oracle H)
```

### `(∀a.p a) → X` is a `p`-oracle sheaf for all `X`

This is Example 4.9 of {{#cite AB26}}.

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} (p : A → Prop l2)
  (𝒪ₚ : oracle-modality l2 l3 (l1 ⊔ l2 ⊔ l4) p)
  (X : UU l4)
  where

  map-has-oracle-sheaf-structure-function-type-∀-oracle :
    (a : A) →
    (type-Prop (p a) → ((b : A) → type-Prop (p b)) → X) →
    (((b : A) → type-Prop (p b)) → X)
  map-has-oracle-sheaf-structure-function-type-∀-oracle a h f =
    h (f a) f

  compute-map-has-oracle-sheaf-structure-function-type-∀-oracle :
    (a : A)
    (h : type-Prop (p a) → ((b : A) → type-Prop (p b)) → X)
    (u : type-Prop (p a)) →
    map-has-oracle-sheaf-structure-function-type-∀-oracle a h ＝ h u
  compute-map-has-oracle-sheaf-structure-function-type-∀-oracle a h u =
    eq-htpy (λ f → ap (ev f) (ap h (eq-type-Prop (p a))))

  map-Id-has-oracle-sheaf-structure-function-type-∀-oracle :
    (x y : ((b : A) → type-Prop (p b)) → X) (a : A) →
    (type-Prop (p a) → x ＝ y) → x ＝ y
  map-Id-has-oracle-sheaf-structure-function-type-∀-oracle x y a f =
    eq-htpy (λ g → ap (ev g) (f (g a)))

  has-oracle-sheaf-structure-function-type-∀-oracle :
    has-oracle-sheaf-structure p 𝒪ₚ (((b : A) → type-Prop (p b)) → X)
  has-oracle-sheaf-structure-function-type-∀-oracle =
    ( map-has-oracle-sheaf-structure-function-type-∀-oracle ,
      compute-map-has-oracle-sheaf-structure-function-type-∀-oracle ,
      map-Id-has-oracle-sheaf-structure-function-type-∀-oracle)

  is-oracle-sheaf-function-type-∀-oracle :
    is-oracle-sheaf p 𝒪ₚ (((b : A) → type-Prop (p b)) → X)
  is-oracle-sheaf-function-type-∀-oracle =
    is-oracle-sheaf-has-oracle-sheaf-structure p 𝒪ₚ
      ( ((b : A) → type-Prop (p b)) → X)
      ( has-oracle-sheaf-structure-function-type-∀-oracle)

  function-type-∀-oracle-oracle-sheaf :
    oracle-sheaf (l1 ⊔ l2 ⊔ l4) p 𝒪ₚ
  function-type-∀-oracle-oracle-sheaf =
    ( (((b : A) → type-Prop (p b)) → X) ,
      is-oracle-sheaf-function-type-∀-oracle)
```

### If `p a` holds for all `a`, then every type is a `p`-oracle sheaf

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} (p : A → Prop l2)
  (𝒪ₚ : oracle-modality l2 l3 (l1 ⊔ l2 ⊔ l4) p)
  (u : (a : A) → type-Prop (p a))
  (X : UU l4)
  where

  retract-is-full-oracle-function-type-∀-oracle :
    (X : UU l4) → X retract-of (((b : A) → type-Prop (p b)) → X)
  retract-is-full-oracle-function-type-∀-oracle X =
    ( diagonal-exponential X ((b : A) → type-Prop (p b)) , ev u , refl-htpy)

  is-oracle-sheaf-is-full-oracle :
    (X : UU l4) → is-oracle-sheaf p 𝒪ₚ X
  is-oracle-sheaf-is-full-oracle X =
    is-oracle-sheaf-retract p 𝒪ₚ
      ( retract-is-full-oracle-function-type-∀-oracle X)
      ( is-oracle-sheaf-function-type-∀-oracle p 𝒪ₚ X)
```

## See also

- The type of [oracle stable propositions](logic.oracle-stable-propositions.md)
  is an oracle sheaf.

## References

{{#bibliography}}
