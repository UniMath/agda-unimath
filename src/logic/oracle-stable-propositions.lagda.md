# Oracle stable propositions

```agda
module logic.oracle-stable-propositions where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.diagonal-maps-of-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.evaluation-functions
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositional-extensionality
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.retractions
open import foundation.sections
open import foundation.sets
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import logic.oracle-modalities
open import logic.oracle-sheaves

open import orthogonal-factorization-systems.null-types
```

</details>

## Idea

Given an oracle `p : A → Prop`, an
{{#concept "oracle stable proposition" Agda=Oracle-Stable-Prop}} can be
presented in three equivalent ways:

1. as a [proposition](foundation-core.propositions.md) `s` equipped with a map
   `𝒪ₚ s → s` where `𝒪ₚ` is the [oracle modality](logic.oracle-modalities.md)
   associated to `p`.

2. as a proposition `s` equipped with operations `(a : A) → (p a → s) → s`

3. as a proposition `s` that is
   [null](orthogonal-factorization-systems.null-types.md) at each `p a`.

This file develops these three presentations, and shows that the collection of
oracle stable propositions forms an [oracle sheaf](logic.oracle-sheaves.md),
Corollary 4.3 {{#cite AB26}}.

## Definitions

### Oracle stable propositions

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} (p : A → Prop l2)
  (𝒪ₚ : oracle-modality l3 l4 l5 p)
  where

  is-oracle-stable-type-Prop : Prop l3 → UU (l3 ⊔ l4)
  is-oracle-stable-type-Prop s =
    type-oracle-modality p 𝒪ₚ (type-Prop s) → type-Prop s

  is-prop-is-oracle-stable-type-Prop :
    (s : Prop l3) → is-prop (is-oracle-stable-type-Prop s)
  is-prop-is-oracle-stable-type-Prop s =
    is-prop-function-type (is-prop-type-Prop s)

  is-oracle-stable-Prop : Prop l3 → Prop (l3 ⊔ l4)
  is-oracle-stable-Prop s =
    ( is-oracle-stable-type-Prop s ,
      is-prop-is-oracle-stable-type-Prop s)

  Oracle-Stable-Prop : UU (lsuc l3 ⊔ l4)
  Oracle-Stable-Prop = type-subtype (is-oracle-stable-Prop)

  prop-Oracle-Stable-Prop :
    Oracle-Stable-Prop → Prop l3
  prop-Oracle-Stable-Prop = pr1

  is-stable-Oracle-Stable-Prop :
    (s : Oracle-Stable-Prop) →
    is-oracle-stable-type-Prop (prop-Oracle-Stable-Prop s)
  is-stable-Oracle-Stable-Prop = pr2
```

### Ask stable propositions

```agda
module _
  {l1 l2 l3 : Level}
  {A : UU l1} (p : A → Prop l2)
  where

  is-oracle-ask-stable-type-Prop : Prop l3 → UU (l1 ⊔ l2 ⊔ l3)
  is-oracle-ask-stable-type-Prop s =
    (a : A) → (type-Prop (p a) → type-Prop s) → type-Prop s

  is-prop-is-oracle-ask-stable-type-Prop :
    (s : Prop l3) → is-prop (is-oracle-ask-stable-type-Prop s)
  is-prop-is-oracle-ask-stable-type-Prop s =
    is-prop-Π (λ _ → is-prop-function-type (is-prop-type-Prop s))

  is-oracle-ask-stable-Prop : Prop l3 → Prop (l1 ⊔ l2 ⊔ l3)
  is-oracle-ask-stable-Prop s =
    ( is-oracle-ask-stable-type-Prop s ,
      is-prop-is-oracle-ask-stable-type-Prop s)

Oracle-Ask-Stable-Prop :
  {l1 l2 : Level} (l3 : Level)
  {A : UU l1} (p : A → Prop l2) → UU (l1 ⊔ l2 ⊔ lsuc l3)
Oracle-Ask-Stable-Prop l3 p =
  type-subtype (is-oracle-ask-stable-Prop {l3 = l3} p)

module _
  {l1 l2 l3 : Level}
  {A : UU l1} (p : A → Prop l2)
  where

  prop-Oracle-Ask-Stable-Prop :
    Oracle-Ask-Stable-Prop l3 p → Prop l3
  prop-Oracle-Ask-Stable-Prop = pr1

  type-Oracle-Ask-Stable-Prop :
    Oracle-Ask-Stable-Prop l3 p → UU l3
  type-Oracle-Ask-Stable-Prop = type-Prop ∘ prop-Oracle-Ask-Stable-Prop

  is-oracle-ask-stable-Oracle-Ask-Stable-Prop :
    (s : Oracle-Ask-Stable-Prop l3 p) →
    is-oracle-ask-stable-type-Prop p (prop-Oracle-Ask-Stable-Prop s)
  is-oracle-ask-stable-Oracle-Ask-Stable-Prop = pr2
```

### Oracle null types

```agda
module _
  {l1 l2 l3 : Level}
  {A : UU l1} (p : A → Prop l2)
  where

  is-oracle-null : UU l3 → UU (l1 ⊔ l2 ⊔ l3)
  is-oracle-null X =
    (a : A) → is-null (type-Prop (p a)) X

  is-prop-is-oracle-null :
    (X : UU l3) → is-prop (is-oracle-null X)
  is-prop-is-oracle-null X =
    is-prop-Π (λ a → is-prop-is-null (type-Prop (p a)) X)
```

### Oracle null propositions

```agda
module _
  {l1 l2 l3 : Level}
  {A : UU l1} (p : A → Prop l2)
  where

  is-oracle-null-type-Prop : Prop l3 → UU (l1 ⊔ l2 ⊔ l3)
  is-oracle-null-type-Prop s =
    is-oracle-null p (type-Prop s)

  is-prop-is-oracle-null-type-Prop :
    (s : Prop l3) → is-prop (is-oracle-null-type-Prop s)
  is-prop-is-oracle-null-type-Prop s =
    is-prop-is-oracle-null p (type-Prop s)

  is-oracle-null-Prop : Prop l3 → Prop (l1 ⊔ l2 ⊔ l3)
  is-oracle-null-Prop s =
    ( is-oracle-null-type-Prop s ,
      is-prop-is-oracle-null-type-Prop s)

Oracle-Null-Prop :
  {l1 l2 : Level} (l3 : Level)
  {A : UU l1} (p : A → Prop l2) →
  UU (l1 ⊔ l2 ⊔ lsuc l3)
Oracle-Null-Prop l3 p =
  type-subtype (is-oracle-null-Prop {l3 = l3} p)

module _
  {l1 l2 l3 : Level}
  {A : UU l1} (p : A → Prop l2)
  where

  prop-Oracle-Null-Prop :
    Oracle-Null-Prop l3 p → Prop l3
  prop-Oracle-Null-Prop = pr1

  type-Oracle-Null-Prop :
    Oracle-Null-Prop l3 p → UU l3
  type-Oracle-Null-Prop =
    type-Prop ∘ prop-Oracle-Null-Prop

  is-oracle-null-type-Oracle-Null-Prop :
    (s : Oracle-Null-Prop l3 p) →
    is-oracle-null-type-Prop p (prop-Oracle-Null-Prop s)
  is-oracle-null-type-Oracle-Null-Prop = pr2
```

## Properties

### Oracle null types are closed under identity types

```agda
module _
  {l1 l2 l3 : Level}
  {A : UU l1} (p : A → Prop l2)
  {X : UU l3}
  where

  is-oracle-null-Id :
    is-oracle-null p X →
    (x y : X) →
    is-oracle-null p (x ＝ y)
  is-oracle-null-Id H x y a =
    is-null-Id (H a) x y
```

### Oracle sheaves are oracle null

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} (p : A → Prop l2)
  (𝒪ₚ : oracle-modality l2 l3 l4 p)
  {X : UU l5}
  where

  is-oracle-null-is-oracle-sheaf :
    is-oracle-sheaf p 𝒪ₚ X →
    is-oracle-null p X
  is-oracle-null-is-oracle-sheaf H a =
    H (p a) (is-dense-self-oracle-modality p 𝒪ₚ a)

  is-oracle-null-Id-is-oracle-sheaf :
    is-oracle-sheaf p 𝒪ₚ X →
    (x y : X) →
    is-oracle-null p (x ＝ y)
  is-oracle-null-Id-is-oracle-sheaf H x y =
    is-oracle-null-Id p (is-oracle-null-is-oracle-sheaf H) x y
```

### Ask stable propositions are oracle null

```agda
module _
  {l1 l2 l3 : Level}
  {A : UU l1} (p : A → Prop l2)
  where

  is-oracle-null-type-Oracle-Ask-Stable-Prop :
    (s : Oracle-Ask-Stable-Prop l3 p) →
    is-oracle-null p (type-Oracle-Ask-Stable-Prop p s)
  is-oracle-null-type-Oracle-Ask-Stable-Prop s a =
    is-equiv-is-invertible
      ( is-oracle-ask-stable-Oracle-Ask-Stable-Prop p s a)
      ( λ h → eq-htpy (λ u → eq-type-Prop (prop-Oracle-Ask-Stable-Prop p s)))
      ( λ x → eq-type-Prop (prop-Oracle-Ask-Stable-Prop p s))
```

### Oracle null propositions are ask stable

```agda
module _
  {l1 l2 l3 : Level}
  {A : UU l1} (p : A → Prop l2)
  where

  is-oracle-ask-stable-is-oracle-null-type-Prop :
    (s : Prop l3) →
    is-oracle-null-type-Prop p s →
    is-oracle-ask-stable-type-Prop p s
  is-oracle-ask-stable-is-oracle-null-type-Prop s H =
    map-inv-is-equiv ∘ H
```

### Oracle stable propositions are ask stable

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} (p : A → Prop l2)
  (𝒪ₚ : oracle-modality l3 l4 l5 p)
  where

  is-oracle-ask-stable-is-oracle-stable-type-Prop :
    (s : Prop l3) →
    is-oracle-stable-type-Prop p 𝒪ₚ s →
    is-oracle-ask-stable-type-Prop p s
  is-oracle-ask-stable-is-oracle-stable-type-Prop s H a f =
    H ( ask-oracle-modality p 𝒪ₚ (type-Prop s) a
        ( unit-oracle-modality p 𝒪ₚ (type-Prop s) ∘ f))
```

### Ask stable propositions are oracle stable

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} (p : A → Prop l2)
  (𝒪ₚ : oracle-modality l3 l4 l3 p)
  where

  is-oracle-stable-is-oracle-ask-stable-type-Prop :
    (s : Prop l3) →
    is-oracle-ask-stable-type-Prop p s →
    is-oracle-stable-type-Prop p 𝒪ₚ s
  is-oracle-stable-is-oracle-ask-stable-type-Prop s H =
    rec-oracle-modality p 𝒪ₚ (type-Prop s)
      ( s)
      ( id)
      ( λ a _ f* → H a f*)
```

### The type of oracle null and ask stable propositions are equivalent

```agda
module _
  {l1 l2 l3 : Level}
  {A : UU l1} (p : A → Prop l2)
  where

  has-same-elements-Oracle-Null-Prop-Oracle-Ask-Stable-Prop :
    has-same-elements-subtype
      ( is-oracle-null-Prop {l3 = l3} p)
      ( is-oracle-ask-stable-Prop {l3 = l3} p)
  pr1 (has-same-elements-Oracle-Null-Prop-Oracle-Ask-Stable-Prop s) =
    is-oracle-ask-stable-is-oracle-null-type-Prop p s
  pr2 (has-same-elements-Oracle-Null-Prop-Oracle-Ask-Stable-Prop s) H =
    is-oracle-null-type-Oracle-Ask-Stable-Prop p (s , H)

  equiv-Oracle-Null-Prop-Oracle-Ask-Stable-Prop :
    Oracle-Null-Prop l3 p ≃ Oracle-Ask-Stable-Prop l3 p
  equiv-Oracle-Null-Prop-Oracle-Ask-Stable-Prop =
    equiv-has-same-elements-type-subtype
      ( is-oracle-null-Prop p)
      ( is-oracle-ask-stable-Prop p)
      has-same-elements-Oracle-Null-Prop-Oracle-Ask-Stable-Prop
```

### The type of oracle stable and ask stable propositions are equivalent

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} (p : A → Prop l2)
  (𝒪ₚ : oracle-modality l3 l4 (l3 ⊔ l5) p)
  where

  has-same-elements-Oracle-Stable-Prop-Oracle-Ask-Stable-Prop :
    has-same-elements-subtype
      ( is-oracle-stable-Prop p 𝒪ₚ)
      ( is-oracle-ask-stable-Prop p)
  pr1 (has-same-elements-Oracle-Stable-Prop-Oracle-Ask-Stable-Prop s) =
    is-oracle-ask-stable-is-oracle-stable-type-Prop p 𝒪ₚ s
  pr2 (has-same-elements-Oracle-Stable-Prop-Oracle-Ask-Stable-Prop s) =
    is-oracle-stable-is-oracle-ask-stable-type-Prop p
      ( lower-oracle-modality l3 l5 p 𝒪ₚ)
      ( s)

  equiv-Oracle-Ask-Stable-Prop-Oracle-Stable-Prop :
    Oracle-Stable-Prop p 𝒪ₚ ≃ Oracle-Ask-Stable-Prop l3 p
  equiv-Oracle-Ask-Stable-Prop-Oracle-Stable-Prop =
    equiv-has-same-elements-type-subtype
      ( is-oracle-stable-Prop p 𝒪ₚ)
      ( is-oracle-ask-stable-Prop p)
      ( has-same-elements-Oracle-Stable-Prop-Oracle-Ask-Stable-Prop)
```

### The type of ask stable propositions is oracle null

```agda
module _
  {l1 l2 : Level} (l3 : Level)
  {A : UU l1} (p : A → Prop l2)
  where

  prop-map-Oracle-Ask-Stable-Prop :
    ( a : A) →
    ( type-Prop (p a) → Oracle-Ask-Stable-Prop (l2 ⊔ l3) p) →
    Prop (l2 ⊔ l3)
  prop-map-Oracle-Ask-Stable-Prop a h =
    Π-Prop (type-Prop (p a)) (λ u → prop-Oracle-Ask-Stable-Prop p (h u))

  map-Oracle-Ask-Stable-Prop :
    (a : A) →
    (type-Prop (p a) → Oracle-Ask-Stable-Prop (l2 ⊔ l3) p) →
    Oracle-Ask-Stable-Prop (l2 ⊔ l3) p
  pr1 (map-Oracle-Ask-Stable-Prop a h) =
    prop-map-Oracle-Ask-Stable-Prop a h
  pr2 (map-Oracle-Ask-Stable-Prop a h) b k u =
    is-oracle-ask-stable-Oracle-Ask-Stable-Prop p (h u) b (λ v → k v u)

  eq-prop-map-Oracle-Ask-Stable-Prop :
    (a : A) (h : type-Prop (p a) → Oracle-Ask-Stable-Prop (l2 ⊔ l3) p)
    (u : type-Prop (p a)) →
    prop-map-Oracle-Ask-Stable-Prop a h ＝
    prop-Oracle-Ask-Stable-Prop p (h u)
  eq-prop-map-Oracle-Ask-Stable-Prop a h u =
    eq-iff
      ( ev u)
      ( λ x v →
        tr
          ( type-Prop)
          ( ap
            ( prop-Oracle-Ask-Stable-Prop p)
            ( ap h (eq-type-Prop (p a))))
          ( x))

  compute-map-Oracle-Ask-Stable-Prop :
    (a : A) (h : type-Prop (p a) → Oracle-Ask-Stable-Prop (l2 ⊔ l3) p)
    (u : type-Prop (p a)) →
    map-Oracle-Ask-Stable-Prop a h ＝ h u
  compute-map-Oracle-Ask-Stable-Prop a h u =
    eq-type-subtype
      ( is-oracle-ask-stable-Prop p)
      ( eq-prop-map-Oracle-Ask-Stable-Prop a h u)

  map-Id-Oracle-Ask-Stable-Prop :
    (x y : Oracle-Ask-Stable-Prop (l2 ⊔ l3) p) (a : A) →
    (type-Prop (p a) → x ＝ y) → x ＝ y
  map-Id-Oracle-Ask-Stable-Prop x y a f =
    eq-type-subtype
      ( is-oracle-ask-stable-Prop p)
      ( eq-iff
        ( λ u →
          is-oracle-ask-stable-Oracle-Ask-Stable-Prop p y a
            ( λ v →
              tr
                ( type-Prop)
                ( ap (prop-Oracle-Ask-Stable-Prop p) (f v))
                ( u)))
        ( λ u →
          is-oracle-ask-stable-Oracle-Ask-Stable-Prop p x a
            ( λ v →
              tr
                ( type-Prop)
                ( inv (ap (prop-Oracle-Ask-Stable-Prop p) (f v)))
                ( u))))
```

```agda
module _
  {l1 l2 l3 : Level}
  {A : UU l1} (p : A → Prop l2)
  where

  is-retraction-map-Oracle-Ask-Stable-Prop :
    (a : A) →
    is-retraction
      ( diagonal-exponential
        ( Oracle-Ask-Stable-Prop (l2 ⊔ l3) p)
        ( type-Prop (p a)))
      ( map-Oracle-Ask-Stable-Prop l3 p a)
  is-retraction-map-Oracle-Ask-Stable-Prop a x =
    map-Id-Oracle-Ask-Stable-Prop l3 p
      ( map-Oracle-Ask-Stable-Prop l3
        ( p)
        ( a)
        ( diagonal-exponential
          ( Oracle-Ask-Stable-Prop (l2 ⊔ l3) p)
          ( type-Prop (p a))
          ( x)))
      ( x)
      ( a)
      ( compute-map-Oracle-Ask-Stable-Prop l3
        ( p)
        ( a)
        ( diagonal-exponential
          ( Oracle-Ask-Stable-Prop (l2 ⊔ l3) p)
          ( type-Prop (p a))
          ( x)))

  is-section-map-Oracle-Ask-Stable-Prop :
    (a : A) →
    is-section
      ( diagonal-exponential
        ( Oracle-Ask-Stable-Prop (l2 ⊔ l3) p)
        ( type-Prop (p a)))
      ( map-Oracle-Ask-Stable-Prop l3 p a)
  is-section-map-Oracle-Ask-Stable-Prop a h =
    eq-htpy (compute-map-Oracle-Ask-Stable-Prop l3 p a h)

  is-oracle-null-Oracle-Ask-Stable-Prop :
    is-oracle-null p (Oracle-Ask-Stable-Prop (l2 ⊔ l3) p)
  is-oracle-null-Oracle-Ask-Stable-Prop a =
    is-equiv-is-invertible
      ( map-Oracle-Ask-Stable-Prop l3 p a)
      ( is-section-map-Oracle-Ask-Stable-Prop a)
      ( is-retraction-map-Oracle-Ask-Stable-Prop a)
```

### The type of ask stable propositions form an oracle sheaf

```agda
module _
  {l1 l2 l3 : Level} (l4 : Level)
  {A : UU l1} (p : A → Prop l2)
  (𝒪ₚ : oracle-modality l2 l3 (l1 ⊔ lsuc l2 ⊔ lsuc l4) p)
  where

  has-structure-Oracle-Ask-Stable-Prop :
    has-oracle-sheaf-structure p 𝒪ₚ (Oracle-Ask-Stable-Prop (l2 ⊔ l4) p)
  has-structure-Oracle-Ask-Stable-Prop =
    ( map-Oracle-Ask-Stable-Prop (l2 ⊔ l4) p ,
      compute-map-Oracle-Ask-Stable-Prop (l2 ⊔ l4) p ,
      map-Id-Oracle-Ask-Stable-Prop (l2 ⊔ l4) p)

  is-oracle-sheaf-Oracle-Ask-Stable-Prop :
    is-oracle-sheaf p 𝒪ₚ (Oracle-Ask-Stable-Prop (l2 ⊔ l4) p)
  is-oracle-sheaf-Oracle-Ask-Stable-Prop =
    is-oracle-sheaf-has-oracle-sheaf-structure p 𝒪ₚ
      ( Oracle-Ask-Stable-Prop (l2 ⊔ l4) p)
      ( has-structure-Oracle-Ask-Stable-Prop)

  oracle-sheaf-Oracle-Ask-Stable-Prop :
    oracle-sheaf (l1 ⊔ lsuc l2 ⊔ lsuc l4) p 𝒪ₚ
  oracle-sheaf-Oracle-Ask-Stable-Prop =
    ( Oracle-Ask-Stable-Prop (l2 ⊔ l4) p ,
      is-oracle-sheaf-Oracle-Ask-Stable-Prop)
```

### The type of oracle null propositions is oracle null

```agda
module _
  {l1 l2 l3 : Level}
  {A : UU l1} (p : A → Prop l2)
  where

  is-oracle-null-Oracle-Null-Prop :
    is-oracle-null p (Oracle-Null-Prop (l2 ⊔ l3) p)
  is-oracle-null-Oracle-Null-Prop a =
    is-null-equiv-base
      ( equiv-Oracle-Null-Prop-Oracle-Ask-Stable-Prop p)
      ( is-oracle-null-Oracle-Ask-Stable-Prop {l3 = l3} p a)
```

### The type of oracle null propositions form an oracle sheaf

```agda
module _
  {l1 l2 l3 : Level} (l4 : Level)
  {A : UU l1} (p : A → Prop l2)
  (𝒪ₚ : oracle-modality l2 l3 (l1 ⊔ lsuc l2 ⊔ lsuc l4) p)
  where

  is-oracle-sheaf-Oracle-Null-Prop :
    is-oracle-sheaf p 𝒪ₚ (Oracle-Null-Prop (l2 ⊔ l4) p)
  is-oracle-sheaf-Oracle-Null-Prop =
    is-oracle-sheaf-equiv p 𝒪ₚ
      ( equiv-Oracle-Null-Prop-Oracle-Ask-Stable-Prop p)
      ( is-oracle-sheaf-Oracle-Ask-Stable-Prop l4 p 𝒪ₚ)

  oracle-sheaf-Oracle-Null-Prop :
    oracle-sheaf (l1 ⊔ lsuc l2 ⊔ lsuc l4) p 𝒪ₚ
  oracle-sheaf-Oracle-Null-Prop =
    ( Oracle-Null-Prop (l2 ⊔ l4) p ,
      is-oracle-sheaf-Oracle-Null-Prop)
```

### The type of oracle stable propositions form an oracle sheaf

```agda
module _
  {l1 l2 l3 : Level} (l4 : Level)
  {A : UU l1} (p : A → Prop l2)
  (𝒪ₚ : oracle-modality l2 l3 (l1 ⊔ lsuc l2 ⊔ lsuc l4 ⊔ l3) p)
  where

  is-oracle-sheaf-Oracle-Ask-Stable-Prop-at-larger-level :
    is-oracle-sheaf p 𝒪ₚ (Oracle-Ask-Stable-Prop (l2 ⊔ l4) p)
  is-oracle-sheaf-Oracle-Ask-Stable-Prop-at-larger-level =
    is-oracle-sheaf-Oracle-Ask-Stable-Prop l4 p
      ( lower-oracle-modality (l1 ⊔ lsuc l2 ⊔ lsuc l4) l3 p 𝒪ₚ)
```

```agda
module _
  {l1 l2 l3 : Level}
  {A : UU l1} (p : A → Prop l2)
  (𝒪ₚ : oracle-modality l2 l3 (l1 ⊔ lsuc l2 ⊔ l3) p)
  where

  is-oracle-sheaf-Oracle-Stable-Prop :
    is-oracle-sheaf p 𝒪ₚ (Oracle-Stable-Prop p 𝒪ₚ)
  is-oracle-sheaf-Oracle-Stable-Prop =
    is-oracle-sheaf-equiv p 𝒪ₚ
      ( equiv-Oracle-Ask-Stable-Prop-Oracle-Stable-Prop p 𝒪ₚ)
      ( is-oracle-sheaf-Oracle-Ask-Stable-Prop-at-larger-level lzero p 𝒪ₚ)

  oracle-sheaf-Oracle-Stable-Prop :
    oracle-sheaf (lsuc l2 ⊔ l3) p 𝒪ₚ
  oracle-sheaf-Oracle-Stable-Prop =
    ( Oracle-Stable-Prop p 𝒪ₚ , is-oracle-sheaf-Oracle-Stable-Prop)
```

### Sets that are oracle sheaves have oracle stable identity types

```agda
module _
  {l1 l2 l3 : Level}
  {A : UU l1} (p : A → Prop l2)
  (𝒪ₚ : oracle-modality l2 l3 (l1 ⊔ lsuc l2 ⊔ l3) p)
  (X : Set l2)
  (H : is-oracle-sheaf p 𝒪ₚ (type-Set X))
  where

  is-oracle-separated-is-oracle-sheaf-type-Set :
    (x y : type-Set X) →
    is-oracle-stable-type-Prop p 𝒪ₚ (Id-Prop X x y)
  is-oracle-separated-is-oracle-sheaf-type-Set x y =
    is-oracle-stable-is-oracle-ask-stable-type-Prop p
      ( lower-oracle-modality l2 (l1 ⊔ lsuc l2 ⊔ l3) p 𝒪ₚ)
      ( Id-Prop X x y)
      ( is-oracle-ask-stable-is-oracle-null-type-Prop p
        ( Id-Prop X x y)
        ( is-oracle-null-Id-is-oracle-sheaf p 𝒪ₚ H x y))
```

## References

{{#bibliography}}
