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

   ```text
     𝒪ₚ s → s
   ```

   where `𝒪ₚ` is the [oracle modality](logic.oracle-modalities.md) associated to
   `p`.

2. as a proposition `s` equipped with operations

   ```text
     (a : A) → (p a → s) → s
   ```

3. as a proposition `s` that is
   [null](orthogonal-factorization-systems.null-types.md) at each `p a`.

This file develops these three presentations, and shows that the collection of
oracle stable propositions forms an [oracle sheaf](logic.oracle-sheaves.md),
Corollary 4.3 {{#cite AB26}}.

## Definitions

### Oracle stable propositions

```agda
module _
  {l1 l2 l3 : Level}
  {A : UU l1} (p : A → Prop l2)
  (𝒪ₚ : oracle-modality l2 l3 (l1 ⊔ lsuc l2 ⊔ l3) p)
  where

  is-oracle-stable-type-Prop : Prop l2 → UU (l2 ⊔ l3)
  is-oracle-stable-type-Prop s =
    type-oracle-modality p 𝒪ₚ (type-Prop s) → type-Prop s

  is-prop-is-oracle-stable-type-Prop :
    (s : Prop l2) → is-prop (is-oracle-stable-type-Prop s)
  is-prop-is-oracle-stable-type-Prop s =
    is-prop-function-type (is-prop-type-Prop s)

  is-oracle-stable-Prop : Prop l2 → Prop (l2 ⊔ l3)
  is-oracle-stable-Prop s =
    ( is-oracle-stable-type-Prop s ,
      is-prop-is-oracle-stable-type-Prop s)

  Oracle-Stable-Prop : UU (lsuc l2 ⊔ l3)
  Oracle-Stable-Prop = type-subtype (is-oracle-stable-Prop)

  prop-Oracle-Stable-Prop :
    Oracle-Stable-Prop → Prop l2
  prop-Oracle-Stable-Prop = pr1

  is-stable-Oracle-Stable-Prop :
    (s : Oracle-Stable-Prop) →
    is-oracle-stable-type-Prop (prop-Oracle-Stable-Prop s)
  is-stable-Oracle-Stable-Prop = pr2
```

### Ask stable propositions

```agda
module _
  {l1 l2 : Level}
  {A : UU l1} (p : A → Prop l2)
  where

  is-oracle-ask-stable-type-Prop : Prop l2 → UU (l1 ⊔ l2)
  is-oracle-ask-stable-type-Prop s =
    (a : A) → (type-Prop (p a) → type-Prop s) → type-Prop s

  is-prop-is-oracle-ask-stable-type-Prop :
    (s : Prop l2) → is-prop (is-oracle-ask-stable-type-Prop s)
  is-prop-is-oracle-ask-stable-type-Prop s =
    is-prop-Π (λ _ → is-prop-function-type (is-prop-type-Prop s))

  is-oracle-ask-stable-Prop : Prop l2 → Prop (l1 ⊔ l2)
  is-oracle-ask-stable-Prop s =
    ( is-oracle-ask-stable-type-Prop s ,
      is-prop-is-oracle-ask-stable-type-Prop s)

  Oracle-Ask-Stable-Prop : UU (l1 ⊔ lsuc l2)
  Oracle-Ask-Stable-Prop = type-subtype (is-oracle-ask-stable-Prop)

  prop-Oracle-Ask-Stable-Prop :
    Oracle-Ask-Stable-Prop → Prop l2
  prop-Oracle-Ask-Stable-Prop = pr1

  is-oracle-ask-stable-Oracle-Ask-Stable-Prop :
    (s : Oracle-Ask-Stable-Prop) →
    is-oracle-ask-stable-type-Prop (prop-Oracle-Ask-Stable-Prop s)
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
  {l1 l2 : Level}
  {A : UU l1} (p : A → Prop l2)
  where

  is-oracle-null-type-Prop : Prop l2 → UU (l1 ⊔ l2)
  is-oracle-null-type-Prop s =
    is-oracle-null p (type-Prop s)

  is-prop-is-oracle-null-type-Prop :
    (s : Prop l2) → is-prop (is-oracle-null-type-Prop s)
  is-prop-is-oracle-null-type-Prop s =
    is-prop-is-oracle-null p (type-Prop s)

  is-oracle-null-Prop : Prop l2 → Prop (l1 ⊔ l2)
  is-oracle-null-Prop s =
    ( is-oracle-null-type-Prop s ,
      is-prop-is-oracle-null-type-Prop s)

  Oracle-Null-Prop : UU (l1 ⊔ lsuc l2)
  Oracle-Null-Prop = type-subtype (is-oracle-null-Prop)

  prop-Oracle-Null-Prop :
    Oracle-Null-Prop → Prop l2
  prop-Oracle-Null-Prop = pr1

  is-oracle-null-type-Oracle-Null-Prop :
    (s : Oracle-Null-Prop) →
    is-oracle-null-type-Prop (prop-Oracle-Null-Prop s)
  is-oracle-null-type-Oracle-Null-Prop = pr2
```

## Properties

### Ask stable propositions are oracle null

```agda
module _
  {l1 l2 : Level}
  {A : UU l1} (p : A → Prop l2)
  where

  is-oracle-null-type-Oracle-Ask-Stable-Prop :
    (s : Oracle-Ask-Stable-Prop p) →
    is-oracle-null p (type-Prop (prop-Oracle-Ask-Stable-Prop p s))
  is-oracle-null-type-Oracle-Ask-Stable-Prop s a =
    is-equiv-is-invertible
      ( is-oracle-ask-stable-Oracle-Ask-Stable-Prop p s a)
      ( λ h → eq-htpy (λ u → eq-type-Prop (prop-Oracle-Ask-Stable-Prop p s)))
      ( λ x → eq-type-Prop (prop-Oracle-Ask-Stable-Prop p s))
```

### Oracle null propositions are ask stable

```agda
module _
  {l1 l2 : Level}
  {A : UU l1} (p : A → Prop l2)
  where

  is-oracle-ask-stable-is-oracle-null-type-Prop :
    (s : Prop l2) →
    is-oracle-null-type-Prop p s →
    is-oracle-ask-stable-type-Prop p s
  is-oracle-ask-stable-is-oracle-null-type-Prop s H =
    map-inv-is-equiv ∘ H
```

### Oracle stable propositions are ask stable

```agda
module _
  {l1 l2 l3 : Level}
  {A : UU l1} (p : A → Prop l2)
  (𝒪ₚ : oracle-modality l2 l3 (l1 ⊔ lsuc l2 ⊔ l3) p)
  where

  is-oracle-ask-stable-is-oracle-stable-type-Prop :
    (s : Prop l2) →
    is-oracle-stable-type-Prop p 𝒪ₚ s →
    is-oracle-ask-stable-type-Prop p s
  is-oracle-ask-stable-is-oracle-stable-type-Prop s H a f =
    H ( ask-oracle-modality p 𝒪ₚ (type-Prop s) a
        ( unit-oracle-modality p 𝒪ₚ (type-Prop s) ∘ f))
```

### Ask stable propositions are oracle stable

```agda
module _
  {l1 l2 l3 : Level}
  {A : UU l1} (p : A → Prop l2)
  (𝒪ₚ : oracle-modality l2 l3 (l1 ⊔ lsuc l2 ⊔ l3) p)
  where

  is-oracle-stable-is-oracle-ask-stable-type-Prop :
    (s : Prop l2) →
    is-oracle-ask-stable-type-Prop p s →
    is-oracle-stable-type-Prop p 𝒪ₚ s
  is-oracle-stable-is-oracle-ask-stable-type-Prop s H =
    map-inv-raise ∘
    rec-oracle-modality p 𝒪ₚ (type-Prop s)
      ( raise-Prop (l1 ⊔ lsuc l2 ⊔ l3) s)
      ( map-raise)
      ( λ a _ f* → map-raise (H a (map-inv-raise ∘ f*)))
```

### The type of oracle null and ask stable propositions are equivalent

```agda
module _
  {l1 l2 : Level}
  {A : UU l1} (p : A → Prop l2)
  where

  has-same-elements-Oracle-Null-Prop-Oracle-Ask-Stable-Prop :
    has-same-elements-subtype
      ( is-oracle-null-Prop p)
      ( is-oracle-ask-stable-Prop p)
  pr1 (has-same-elements-Oracle-Null-Prop-Oracle-Ask-Stable-Prop s) =
    is-oracle-ask-stable-is-oracle-null-type-Prop p s
  pr2 (has-same-elements-Oracle-Null-Prop-Oracle-Ask-Stable-Prop s) H =
    is-oracle-null-type-Oracle-Ask-Stable-Prop p (s , H)

  equiv-Oracle-Null-Prop-Oracle-Ask-Stable-Prop :
    Oracle-Null-Prop p ≃ Oracle-Ask-Stable-Prop p
  equiv-Oracle-Null-Prop-Oracle-Ask-Stable-Prop =
    equiv-has-same-elements-type-subtype
      ( is-oracle-null-Prop p)
      ( is-oracle-ask-stable-Prop p)
      has-same-elements-Oracle-Null-Prop-Oracle-Ask-Stable-Prop
```

### The type of oracle stable and ask stable propositions are equivalent

```agda
module _
  {l1 l2 l3 : Level}
  {A : UU l1} (p : A → Prop l2)
  (𝒪ₚ : oracle-modality l2 l3 (l1 ⊔ lsuc l2 ⊔ l3) p)
  where

  has-same-elements-Oracle-Stable-Prop-Oracle-Ask-Stable-Prop :
    has-same-elements-subtype
      ( is-oracle-stable-Prop p 𝒪ₚ)
      ( is-oracle-ask-stable-Prop p)
  pr1 (has-same-elements-Oracle-Stable-Prop-Oracle-Ask-Stable-Prop s) =
    is-oracle-ask-stable-is-oracle-stable-type-Prop p 𝒪ₚ s
  pr2 (has-same-elements-Oracle-Stable-Prop-Oracle-Ask-Stable-Prop s) =
    is-oracle-stable-is-oracle-ask-stable-type-Prop p 𝒪ₚ s

  equiv-Oracle-Ask-Stable-Prop-Oracle-Stable-Prop :
    Oracle-Stable-Prop p 𝒪ₚ ≃ Oracle-Ask-Stable-Prop p
  equiv-Oracle-Ask-Stable-Prop-Oracle-Stable-Prop =
    equiv-has-same-elements-type-subtype
      ( is-oracle-stable-Prop p 𝒪ₚ)
      ( is-oracle-ask-stable-Prop p)
      has-same-elements-Oracle-Stable-Prop-Oracle-Ask-Stable-Prop
```

### The type of ask stable propositions is oracle null

```agda
module _
  {l1 l2 : Level}
  {A : UU l1} (p : A → Prop l2)
  where

  prop-map-Oracle-Ask-Stable-Prop :
    (a : A) (h : type-Prop (p a) → Oracle-Ask-Stable-Prop p) → Prop l2
  prop-map-Oracle-Ask-Stable-Prop a h =
    Π-Prop (type-Prop (p a)) (λ u → prop-Oracle-Ask-Stable-Prop p (h u))

  map-Oracle-Ask-Stable-Prop :
    (a : A) →
    (type-Prop (p a) → Oracle-Ask-Stable-Prop p) →
    Oracle-Ask-Stable-Prop p
  pr1 (map-Oracle-Ask-Stable-Prop a h) =
    prop-map-Oracle-Ask-Stable-Prop a h
  pr2 (map-Oracle-Ask-Stable-Prop a h) b k u =
    is-oracle-ask-stable-Oracle-Ask-Stable-Prop p (h u) b (λ v → k v u)

  eq-prop-map-Oracle-Ask-Stable-Prop :
    (a : A) (h : type-Prop (p a) → Oracle-Ask-Stable-Prop p)
    (u : type-Prop (p a)) →
    prop-map-Oracle-Ask-Stable-Prop a h ＝
    prop-Oracle-Ask-Stable-Prop p (h u)
  eq-prop-map-Oracle-Ask-Stable-Prop a h u =
    eq-iff
      ( ev u)
      ( λ x v →
        tr
          ( type-Prop)
          ( ap (prop-Oracle-Ask-Stable-Prop p) (ap h (eq-type-Prop (p a))))
          ( x))

  compute-map-Oracle-Ask-Stable-Prop :
    (a : A) (h : type-Prop (p a) → Oracle-Ask-Stable-Prop p)
    (u : type-Prop (p a)) →
    map-Oracle-Ask-Stable-Prop a h ＝ h u
  compute-map-Oracle-Ask-Stable-Prop a h u =
    eq-type-subtype
      ( is-oracle-ask-stable-Prop p)
      ( eq-prop-map-Oracle-Ask-Stable-Prop a h u)

  map-Id-Oracle-Ask-Stable-Prop :
    (x y : Oracle-Ask-Stable-Prop p) (a : A) →
    (type-Prop (p a) → x ＝ y) → x ＝ y
  map-Id-Oracle-Ask-Stable-Prop x y a f =
    eq-type-subtype
      ( is-oracle-ask-stable-Prop p)
      ( eq-iff
        ( λ u →
          is-oracle-ask-stable-Oracle-Ask-Stable-Prop p y a
            ( λ v → tr type-Prop (ap (prop-Oracle-Ask-Stable-Prop p) (f v)) u))
        ( λ u →
          is-oracle-ask-stable-Oracle-Ask-Stable-Prop p x a
            ( λ v →
              tr type-Prop (inv (ap (prop-Oracle-Ask-Stable-Prop p) (f v))) u)))
```

```agda
module _
  {l1 l2 : Level}
  {A : UU l1} (p : A → Prop l2)
  where

  is-retraction-map-Oracle-Ask-Stable-Prop :
    (a : A) →
    is-retraction
      ( diagonal-exponential
        ( Oracle-Ask-Stable-Prop p)
        ( type-Prop (p a)))
      ( map-Oracle-Ask-Stable-Prop p a)
  is-retraction-map-Oracle-Ask-Stable-Prop a x =
    map-Id-Oracle-Ask-Stable-Prop p
      ( map-Oracle-Ask-Stable-Prop
        ( p)
        ( a)
        ( diagonal-exponential (Oracle-Ask-Stable-Prop p) (type-Prop (p a)) x))
      ( x)
      ( a)
      ( compute-map-Oracle-Ask-Stable-Prop
        ( p)
        ( a)
        ( diagonal-exponential (Oracle-Ask-Stable-Prop p) (type-Prop (p a)) x))

  is-section-map-Oracle-Ask-Stable-Prop :
    (a : A) →
    is-section
      ( diagonal-exponential (Oracle-Ask-Stable-Prop p) (type-Prop (p a)))
      ( map-Oracle-Ask-Stable-Prop p a)
  is-section-map-Oracle-Ask-Stable-Prop a h =
    eq-htpy (compute-map-Oracle-Ask-Stable-Prop p a h)

  is-oracle-null-Oracle-Ask-Stable-Prop :
    is-oracle-null p (Oracle-Ask-Stable-Prop p)
  is-oracle-null-Oracle-Ask-Stable-Prop a =
    is-equiv-is-invertible
      ( map-Oracle-Ask-Stable-Prop p a)
      ( is-section-map-Oracle-Ask-Stable-Prop a)
      ( is-retraction-map-Oracle-Ask-Stable-Prop a)
```

### The type of ask stable propositions form an oracle sheaf

```agda
module _
  {l1 l2 l3 : Level}
  {A : UU l1} (p : A → Prop l2)
  (𝒪ₚ : oracle-modality l2 l3 (l1 ⊔ lsuc l2) p)
  where

  has-structure-Oracle-Ask-Stable-Prop :
    has-oracle-sheaf-structure p 𝒪ₚ (Oracle-Ask-Stable-Prop p)
  has-structure-Oracle-Ask-Stable-Prop =
    ( map-Oracle-Ask-Stable-Prop p ,
      compute-map-Oracle-Ask-Stable-Prop p ,
      map-Id-Oracle-Ask-Stable-Prop p)

  is-oracle-sheaf-Oracle-Ask-Stable-Prop :
    is-oracle-sheaf p 𝒪ₚ (Oracle-Ask-Stable-Prop p)
  is-oracle-sheaf-Oracle-Ask-Stable-Prop =
    is-oracle-sheaf-has-oracle-sheaf-structure p 𝒪ₚ
      ( Oracle-Ask-Stable-Prop p)
      ( has-structure-Oracle-Ask-Stable-Prop)

  oracle-sheaf-Oracle-Ask-Stable-Prop :
    oracle-sheaf (l1 ⊔ lsuc l2) p 𝒪ₚ
  oracle-sheaf-Oracle-Ask-Stable-Prop =
    ( Oracle-Ask-Stable-Prop p ,
      is-oracle-sheaf-Oracle-Ask-Stable-Prop)
```

### The type of oracle null propositions is oracle null

```agda
module _
  {l1 l2 : Level}
  {A : UU l1} (p : A → Prop l2)
  where

  is-oracle-null-Oracle-Null-Prop :
    is-oracle-null p (Oracle-Null-Prop p)
  is-oracle-null-Oracle-Null-Prop a =
    is-null-equiv-base
      ( equiv-Oracle-Null-Prop-Oracle-Ask-Stable-Prop p)
      ( is-oracle-null-Oracle-Ask-Stable-Prop p a)
```

### The type of oracle null propositions form an oracle sheaf

```agda
module _
  {l1 l2 l3 : Level}
  {A : UU l1} (p : A → Prop l2)
  (𝒪ₚ : oracle-modality l2 l3 (l1 ⊔ lsuc l2) p)
  where

  is-oracle-sheaf-Oracle-Null-Prop :
    is-oracle-sheaf p 𝒪ₚ (Oracle-Null-Prop p)
  is-oracle-sheaf-Oracle-Null-Prop =
    is-oracle-sheaf-equiv p 𝒪ₚ
      ( equiv-Oracle-Null-Prop-Oracle-Ask-Stable-Prop p)
      ( is-oracle-sheaf-Oracle-Ask-Stable-Prop p 𝒪ₚ)

  oracle-sheaf-Oracle-Null-Prop :
    oracle-sheaf (l1 ⊔ lsuc l2) p 𝒪ₚ
  oracle-sheaf-Oracle-Null-Prop =
    ( Oracle-Null-Prop p ,
      is-oracle-sheaf-Oracle-Null-Prop)
```

### The type of oracle stable propositions form an oracle sheaf

```agda
module _
  {l1 l2 l3 : Level}
  {A : UU l1} (p : A → Prop l2)
  (𝒪ₚ : oracle-modality l2 l3 (l1 ⊔ lsuc l2 ⊔ l3) p)
  where

  is-oracle-sheaf-Oracle-Ask-Stable-Prop-at-larger-level :
    is-oracle-sheaf p 𝒪ₚ (Oracle-Ask-Stable-Prop p)
  is-oracle-sheaf-Oracle-Ask-Stable-Prop-at-larger-level =
    is-oracle-sheaf-Oracle-Ask-Stable-Prop p
      ( lower-oracle-modality
        {l5 = l1 ⊔ lsuc l2}
        {l6 = l3}
        p
        𝒪ₚ)

  is-oracle-sheaf-Oracle-Stable-Prop :
    is-oracle-sheaf p 𝒪ₚ (Oracle-Stable-Prop p 𝒪ₚ)
  is-oracle-sheaf-Oracle-Stable-Prop =
    is-oracle-sheaf-equiv p 𝒪ₚ
      ( equiv-Oracle-Ask-Stable-Prop-Oracle-Stable-Prop p 𝒪ₚ)
      is-oracle-sheaf-Oracle-Ask-Stable-Prop-at-larger-level

  oracle-sheaf-Oracle-Stable-Prop :
    oracle-sheaf (lsuc l2 ⊔ l3) p 𝒪ₚ
  oracle-sheaf-Oracle-Stable-Prop =
    ( Oracle-Stable-Prop p 𝒪ₚ , is-oracle-sheaf-Oracle-Stable-Prop)
```

## References

{{#bibliography}}
