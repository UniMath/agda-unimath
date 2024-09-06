# Cumulative hierarchy

```agda
module set-theory.cumulative-hierarchy where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.booleans
open import foundation.cartesian-product-types
open import foundation.constant-type-families
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.functoriality-propositional-truncation
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositional-extensionality
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.sets
open import foundation.transport-along-identifications
open import foundation.truncated-types
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

The cumulative hierarchy is a model of set theory. Instead of introducing it as
a HIT, as in Section 10.4 of {{#cite UF13}}, we introduce its induction
principle, following {{#cite dJKFX23}}.

## Definitions

### Smaller image

```agda
has-smaller-image :
  { l1 l2 l3 : Level} →
  {A : UU l1} {B : UU l2} {C : UU l3} →
  (A → C) → (B → C) → UU (l1 ⊔ l2 ⊔ l3)
has-smaller-image {l1} {l2} {l3} {A} {B} {C} f g =
  (a : A) → exists-structure B (λ b → g b ＝ f a)

has-same-image :
  { l1 l2 l3 : Level} →
  {A : UU l1} {B : UU l2} {C : UU l3} →
  (A → C) → (B → C) → UU (l1 ⊔ l2 ⊔ l3)
has-same-image {l1} {l2} {l3} {A} {B} {C} f g =
  has-smaller-image f g ×
    has-smaller-image g f
```

### Pseudo cumulative hierarchy

A type is a pseudo cumulative hierarchy if it has the structure of a cumulative
hierarchy, but not necessarily its induction principle.

```agda
has-cumulative-hierarchy-structure :
  {l : Level} → (V : UU (lsuc l)) → UU (lsuc l)
has-cumulative-hierarchy-structure {l} V =
  ( is-set V) ×
    ( Σ ({A : UU l} → (A → V) → V)
      ( λ V-set →
        ( {A B : UU l} (f : A → V) (g : B → V) →
          ( has-same-image f g) → V-set f ＝ V-set g)))

pseudo-cumulative-hierarchy : (l : Level) → UU (lsuc (lsuc l))
pseudo-cumulative-hierarchy (l) =
  Σ (UU (lsuc l)) has-cumulative-hierarchy-structure

module _
  {l : Level} (V : pseudo-cumulative-hierarchy l)
  where

  type-pseudo-cumulative-hierarchy : UU (lsuc l)
  type-pseudo-cumulative-hierarchy = pr1 V

  is-set-pseudo-cumulative-hierarchy :
    is-set type-pseudo-cumulative-hierarchy
  is-set-pseudo-cumulative-hierarchy = pr1 (pr2 V)

  set-pseudo-cumulative-hierarchy :
    { A : UU l} →
    ( A → type-pseudo-cumulative-hierarchy) →
    type-pseudo-cumulative-hierarchy
  set-pseudo-cumulative-hierarchy = pr1 (pr2 (pr2 V))

  set-ext-pseudo-cumulative-hierarchy :
    { A B : UU l} (f : A → type-pseudo-cumulative-hierarchy)
    ( g : B → type-pseudo-cumulative-hierarchy) →
    ( has-same-image f g) →
    set-pseudo-cumulative-hierarchy f ＝ set-pseudo-cumulative-hierarchy g
  set-ext-pseudo-cumulative-hierarchy = pr2 (pr2 (pr2 V))
```

### The induction principle and computation rule of the cumulative hierarchy

```agda
module _
  {l1 : Level} (l2 : Level) (V : pseudo-cumulative-hierarchy l1)
  where
  induction-principle-cumulative-hierarchy : UU (lsuc (l1 ⊔ l2))
  induction-principle-cumulative-hierarchy =
    ( P : type-pseudo-cumulative-hierarchy V → UU l2) →
    ( (x : type-pseudo-cumulative-hierarchy V) → is-set (P x)) →
    ( ρ :
      { A : UU l1} (f : A → type-pseudo-cumulative-hierarchy V) →
      ( (a : A) → P (f a)) → P (set-pseudo-cumulative-hierarchy V f)) →
    ( { A B : UU l1} (f : A → type-pseudo-cumulative-hierarchy V) →
      ( g : B → type-pseudo-cumulative-hierarchy V)
      ( e : has-same-image f g)
      ( IH₁ : (a : A) → P (f a))
      ( IH₂ : (b : B) → P (g b)) →
      ( ( a : A) → exists-structure B (λ b → Σ (f a ＝ g b)
        ( λ p → tr P p (IH₁ a) ＝ IH₂ b))) →
      ( ( b : B) → exists-structure A (λ a →
        Σ (g b ＝ f a) (λ p → tr P p (IH₂ b) ＝ IH₁ a))) →
      tr P (set-ext-pseudo-cumulative-hierarchy V f g e) (ρ f IH₁) ＝ ρ g IH₂) →
    (x : type-pseudo-cumulative-hierarchy V) → P x

  compute-induction-principle-cumulative-hierarchy :
    induction-principle-cumulative-hierarchy → UU (lsuc (l1 ⊔ l2))
  compute-induction-principle-cumulative-hierarchy IP =
    ( P : type-pseudo-cumulative-hierarchy V → UU l2) →
    ( σ : (x : type-pseudo-cumulative-hierarchy V) → is-set (P x)) →
    ( ρ :
      { A : UU l1} (f : A → type-pseudo-cumulative-hierarchy V) →
      ( (a : A) → P (f a)) → P (set-pseudo-cumulative-hierarchy V f)) →
    ( τ :
      { A B : UU l1} (f : A → type-pseudo-cumulative-hierarchy V) →
      ( g : B → type-pseudo-cumulative-hierarchy V)
      ( e : has-same-image f g)
      ( IH₁ : (a : A) → P (f a))
      ( IH₂ : (b : B) → P (g b)) →
      ( (a : A) → exists-structure B (λ b → Σ (f a ＝ g b)
        ( λ p → tr P p (IH₁ a) ＝ IH₂ b))) →
      ( (b : B) → exists-structure A (λ a → Σ (g b ＝ f a)
        (λ p → tr P p (IH₂ b) ＝ IH₁ a))) →
      tr P (set-ext-pseudo-cumulative-hierarchy V f g e) (ρ f IH₁) ＝ ρ g IH₂) →
    { A : UU l1} (f : A → type-pseudo-cumulative-hierarchy V)
    ( IH : (a : A) → P (f a)) →
    IP P σ ρ τ (set-pseudo-cumulative-hierarchy V f) ＝ ρ f IH
```

## Examples

```agda
module _
  {l1 : Level} (V : pseudo-cumulative-hierarchy l1)
  (induction-principle-cumulative-hierarchy-V :
    (l2 : Level) → induction-principle-cumulative-hierarchy l2 V)
  (compute-induction-principle-cumulative-hierarchy-V :
    (l2 : Level) → compute-induction-principle-cumulative-hierarchy l2 V
      (induction-principle-cumulative-hierarchy-V l2))
  where
```

### The empty set

```agda
  empty-set-cumulative-hierarchy : type-pseudo-cumulative-hierarchy V
  empty-set-cumulative-hierarchy =
    set-pseudo-cumulative-hierarchy V (raise-ex-falso l1)
```

### The set containing only the empty set

```agda
  set-empty-set-cumulative-hierarchy : type-pseudo-cumulative-hierarchy V
  set-empty-set-cumulative-hierarchy =
    set-pseudo-cumulative-hierarchy V {raise-unit l1}
      ( λ _ → empty-set-cumulative-hierarchy)
```

## Properties

### Every element of the cumulative hierarchy is given by a function into the cumulative hierarchy

```agda
  underlying-function-cumulative-hierarchy :
    (v : type-pseudo-cumulative-hierarchy V) →
    exists-structure ( UU l1)
      ( λ A →
        Σ ( A → type-pseudo-cumulative-hierarchy V)
          ( λ f → set-pseudo-cumulative-hierarchy V f ＝ v))
  underlying-function-cumulative-hierarchy =
    induction-principle-cumulative-hierarchy-V
      ( lsuc l1) _
      ( λ _ → is-trunc-type-Truncated-Type (set-trunc-Prop _))
      ( λ {A} f H → unit-trunc-Prop (pair A (pair f refl)))
      ( λ f g e IH₁ IH₂ hIH₁ hIH₂ → eq-is-prop is-prop-type-trunc-Prop)
```

### The induction principle simplified for families of propositions

```agda
  prop-ind-principle-cumulative-hierarchy :
    { l2 : Level}
    ( P : type-pseudo-cumulative-hierarchy V → UU l2) →
    ( ( x : type-pseudo-cumulative-hierarchy V) → is-prop (P x)) →
    ( { A : UU l1} (f : A → type-pseudo-cumulative-hierarchy V) →
      ( (a : A) → P (f a)) →
      ( P (set-pseudo-cumulative-hierarchy V f))) →
    ( x : type-pseudo-cumulative-hierarchy V) → P x
  prop-ind-principle-cumulative-hierarchy {l2} P σ ρ =
    induction-principle-cumulative-hierarchy-V l2 P
      ( λ x → is-set-is-prop (σ x)) ρ
      ( λ _ g _ _ _ _ _ → eq-is-prop (σ (set-pseudo-cumulative-hierarchy V g)))

  compute-prop-ind-principle-cumulative-hierarchy :
    { l2 : Level}
    ( P : type-pseudo-cumulative-hierarchy V → UU l2) →
    ( σ : ( x : type-pseudo-cumulative-hierarchy V) → is-prop (P x)) →
    ( ρ :
      { A : UU l1} (f : A → type-pseudo-cumulative-hierarchy V) →
      ( (a : A) → P (f a)) →
      ( P (set-pseudo-cumulative-hierarchy V f))) →
    { A : UU l1} (f : A → type-pseudo-cumulative-hierarchy V)
    ( IH : (a : A) → P (f a)) →
    prop-ind-principle-cumulative-hierarchy
      P σ ρ (set-pseudo-cumulative-hierarchy V f) ＝ ρ f IH
  compute-prop-ind-principle-cumulative-hierarchy {l2} P σ ρ =
    compute-induction-principle-cumulative-hierarchy-V l2 P
      ( λ x → is-set-is-prop (σ x)) ρ
      ( λ _ g _ _ _ _ _ → eq-is-prop (σ (set-pseudo-cumulative-hierarchy V g)))
```

### The recursion principle and its computation rule for the cumulative hierarchy

```agda
  recursion-principle-cumulative-hierarchy :
    { l2 : Level}
    ( X : UU l2) (σ : is-set X)
    ( ρ : {A : UU l1} → (A → type-pseudo-cumulative-hierarchy V) → (A → X) → X)
    ( τ :
      { A B : UU l1} (f : A → type-pseudo-cumulative-hierarchy V)
      ( g : B → type-pseudo-cumulative-hierarchy V)
      ( e : has-same-image f g)
      ( IH₁ : A → X)
      ( IH₂ : B → X) →
      ( (a : A) → exists-structure B (λ b → (f a ＝ g b) × (IH₁ a ＝ IH₂ b))) →
      ( (b : B) → exists-structure A (λ a → (g b ＝ f a) × (IH₂ b ＝ IH₁ a))) →
      ρ f IH₁ ＝ ρ g IH₂) →
    type-pseudo-cumulative-hierarchy V → X
  recursion-principle-cumulative-hierarchy {l2} X σ ρ τ =
    induction-principle-cumulative-hierarchy-V l2 (λ _ → X) (λ _ → σ) ρ τ'
    where
    τ' :
      { A B : UU l1} (f : A → pr1 V) (g : B → pr1 V)
      ( e : has-same-image f g)
      ( IH₁ : (a : A) → X) (IH₂ : (b : B) → X) →
      ( (a : A) → exists-structure B (λ b → Σ (f a ＝ g b)
        (λ p → tr (λ _ → X) p (IH₁ a) ＝ IH₂ b))) →
      ( (b : B) → exists-structure A (λ a → Σ (g b ＝ f a)
        (λ p → tr (λ _ → X) p (IH₂ b) ＝ IH₁ a))) →
      tr (λ _ → X) (pr2 (pr2 (pr2 V)) f g e) (ρ f IH₁) ＝ ρ g IH₂
    τ' {A} {B} f g e IH₁ IH₂ hIH₁ hIH₂ =
      equational-reasoning
        tr (λ _ → X) (pr2 (pr2 (pr2 V)) f g e) (ρ f IH₁)
        ＝ ρ f IH₁
          by tr-constant-type-family path-f-g (ρ f IH₁)
        ＝ ρ g IH₂
          by τ f g e IH₁ IH₂ hIH₁' hIH₂'
      where
      path-f-g :
        set-pseudo-cumulative-hierarchy V f
          ＝ set-pseudo-cumulative-hierarchy V g
      path-f-g = set-ext-pseudo-cumulative-hierarchy V f g e
      hIH₁' :
        (a : A) →
        exists-structure B (λ b → Σ (f a ＝ g b) (λ _ → IH₁ a ＝ IH₂ b))
      hIH₁' a =
        map-trunc-Prop
          ( λ (b , p , q) →
            ( b , p , (inv (tr-constant-type-family p _) ∙ q)))
          ( hIH₁ a)
      hIH₂' :
        (b : B) →
        exists-structure A (λ a → Σ (g b ＝ f a) (λ _ → IH₂ b ＝ IH₁ a))
      hIH₂' b =
        map-trunc-Prop
          ( λ (a , p , q) →
            ( a , p , (inv (tr-constant-type-family p _) ∙ q)))
          ( hIH₂ b)

  compute-recursion-principle-cumulative-hierarchy :
    { l2 : Level} ( X : UU l2) (σ : is-set X)
    ( ρ : {A : UU l1} → (A → type-pseudo-cumulative-hierarchy V) → (A → X) → X)
    ( τ :
      { A B : UU l1} (f : A → type-pseudo-cumulative-hierarchy V)
      ( g : B → type-pseudo-cumulative-hierarchy V)
      ( e : has-same-image f g)
      ( IH₁ : A → X)
      ( IH₂ : B → X) →
      ( ( a : A) → exists-structure B (λ b → (f a ＝ g b) × (IH₁ a ＝ IH₂ b))) →
      ( ( b : B) → exists-structure A (λ a → (g b ＝ f a) × (IH₂ b ＝ IH₁ a))) →
      ρ f IH₁ ＝ ρ g IH₂) →
    {A : UU l1} → (f : A → type-pseudo-cumulative-hierarchy V) → (IH : A → X) →
    recursion-principle-cumulative-hierarchy X σ ρ τ
      ( set-pseudo-cumulative-hierarchy V f) ＝ ρ f IH
  compute-recursion-principle-cumulative-hierarchy {l2} X σ ρ τ =
    compute-induction-principle-cumulative-hierarchy-V
      l2 (λ _ → X) (λ _ → σ) ρ τ'
    where
    τ' :
      { A B : UU l1} (f : A → pr1 V) (g : B → pr1 V)
      ( e : has-same-image f g)
      ( IH₁ : (a : A) → X) (IH₂ : (b : B) → X) →
      ( ( a : A) → exists-structure B (λ b → Σ (f a ＝ g b)
        ( λ p → tr (λ _ → X) p (IH₁ a) ＝ IH₂ b))) →
      ( ( b : B) → exists-structure A (λ a → Σ (g b ＝ f a)
        ( λ p → tr (λ _ → X) p (IH₂ b) ＝ IH₁ a))) →
      tr (λ _ → X) (pr2 (pr2 (pr2 V)) f g e) (ρ f IH₁) ＝ ρ g IH₂
    τ' {A} {B} f g e IH₁ IH₂ hIH₁ hIH₂ =
      equational-reasoning
        tr (λ _ → X) (pr2 (pr2 (pr2 V)) f g e) (ρ f IH₁)
        ＝ ρ f IH₁
          by tr-constant-type-family path-f-g (ρ f IH₁)
        ＝ ρ g IH₂
          by τ f g e IH₁ IH₂ hIH₁' hIH₂'
      where
      path-f-g :
        set-pseudo-cumulative-hierarchy V f
          ＝ set-pseudo-cumulative-hierarchy V g
      path-f-g = set-ext-pseudo-cumulative-hierarchy V f g e
      hIH₁' :
        (a : A) →
        exists-structure B (λ b → Σ (f a ＝ g b) (λ _ → IH₁ a ＝ IH₂ b))
      hIH₁' a =
        map-trunc-Prop
          ( λ (b , p , q) →
            ( b , p , (inv (tr-constant-type-family p _) ∙ q)))
          ( hIH₁ a)
      hIH₂' :
        (b : B) →
        exists-structure A (λ a → Σ (g b ＝ f a) (λ _ → IH₂ b ＝ IH₁ a))
      hIH₂' b =
        map-trunc-Prop
          ( λ (a , p , q) →
            ( a , p , (inv (tr-constant-type-family p _) ∙ q)))
          ( hIH₂ b)
```

A simplification of the recursion principle, when the codomain is `Prop l2`.

```agda
  prop-recursion-principle-cumulative-hierarchy :
    {l2 : Level}
    ( ρ :
      { A : UU l1} → (A → type-pseudo-cumulative-hierarchy V) →
      ( A → Prop l2) → Prop l2)
    ( τ : {A B : UU l1} (f : A → type-pseudo-cumulative-hierarchy V)
      ( g : B → type-pseudo-cumulative-hierarchy V)
      ( e : has-smaller-image f g)
      ( IH₁ : A → Prop l2)
      ( IH₂ : B → Prop l2) →
      ( (a : A) → exists-structure B (λ b → (f a ＝ g b) × (IH₁ a ＝ IH₂ b))) →
      type-Prop (ρ f IH₁) → type-Prop (ρ g IH₂)) →
    type-pseudo-cumulative-hierarchy V → Prop l2
  prop-recursion-principle-cumulative-hierarchy {l2} ρ τ =
    recursion-principle-cumulative-hierarchy (Prop l2)
      is-set-type-Prop ρ τ'
    where
    τ' :
      { A B : UU l1} (f : A → type-pseudo-cumulative-hierarchy V)
      ( g : B → type-pseudo-cumulative-hierarchy V) →
      ( e : has-same-image f g)
      ( IH₁ : A → Prop l2) (IH₂ : B → Prop l2) →
      ( (a : A) → exists-structure B (λ b → (f a ＝ g b) × (IH₁ a ＝ IH₂ b))) →
      ( (b : B) → exists-structure A (λ a → (g b ＝ f a) × (IH₂ b ＝ IH₁ a))) →
      ρ f IH₁ ＝ ρ g IH₂
    τ' f g (e₁ , e₂) IH₁ IH₂ hIH₁ hIH₂ =
      eq-iff (τ f g e₁ IH₁ IH₂ hIH₁) (τ g f e₂ IH₂ IH₁ hIH₂)

  compute-prop-recursion-principle-cumulative-hierarchy :
    {l2 : Level}
    ( ρ :
      { A : UU l1} → (A → type-pseudo-cumulative-hierarchy V) →
      ( A → Prop l2) → Prop l2)
    ( τ :
      { A B : UU l1} (f : A → type-pseudo-cumulative-hierarchy V)
      ( g : B → type-pseudo-cumulative-hierarchy V)
      ( e : has-smaller-image f g)
      ( IH₁ : A → Prop l2)
      ( IH₂ : B → Prop l2) →
      ( (a : A) → exists-structure B (λ b → (f a ＝ g b) × (IH₁ a ＝ IH₂ b))) →
      type-Prop (ρ f IH₁) → type-Prop (ρ g IH₂)) →
    { A : UU l1} → (f : A → type-pseudo-cumulative-hierarchy V) →
    ( IH : A → Prop l2) →
    prop-recursion-principle-cumulative-hierarchy ρ τ
      ( set-pseudo-cumulative-hierarchy V f) ＝ ρ f IH
  compute-prop-recursion-principle-cumulative-hierarchy {l2} ρ τ =
    compute-recursion-principle-cumulative-hierarchy (Prop l2)
      is-set-type-Prop ρ τ'
    where
    τ' :
      { A B : UU l1} (f : A → type-pseudo-cumulative-hierarchy V)
      ( g : B → type-pseudo-cumulative-hierarchy V) →
      ( e : has-same-image f g)
      ( IH₁ : A → Prop l2) (IH₂ : B → Prop l2) →
      ( (a : A) → exists-structure B (λ b → (f a ＝ g b) × (IH₁ a ＝ IH₂ b))) →
      ( (b : B) → exists-structure A (λ a → (g b ＝ f a) × (IH₂ b ＝ IH₁ a))) →
      ρ f IH₁ ＝ ρ g IH₂
    τ' f g (e₁ , e₂) IH₁ IH₂ hIH₁ hIH₂ =
      eq-iff (τ f g e₁ IH₁ IH₂ hIH₁) (τ g f e₂ IH₂ IH₁ hIH₂)
```

Another simplification of the recursion principle, when recursive calls are not
needed.

```agda
  simple-prop-recursion-principle-cumulative-hierarchy :
    {l2 : Level}
    ( ρ : {A : UU l1} → (A → type-pseudo-cumulative-hierarchy V) → Prop l2)
    ( τ :
      { A B : UU l1} (f : A → type-pseudo-cumulative-hierarchy V)
      ( g : B → type-pseudo-cumulative-hierarchy V) →
      ( e : has-smaller-image f g) →
      type-Prop (ρ f) → type-Prop (ρ g)) →
    type-pseudo-cumulative-hierarchy V → Prop l2
  simple-prop-recursion-principle-cumulative-hierarchy {l2} ρ τ =
    prop-recursion-principle-cumulative-hierarchy
      ( λ f _ → ρ f) (λ f g e _ _ _ → τ f g e)

  compute-simple-prop-recursion-principle-cumulative-hierarchy :
    {l2 : Level}
    ( ρ : {A : UU l1} → (A → type-pseudo-cumulative-hierarchy V) → Prop l2)
    ( τ :
      { A B : UU l1} (f : A → type-pseudo-cumulative-hierarchy V)
      ( g : B → type-pseudo-cumulative-hierarchy V) →
      ( e : has-smaller-image f g) →
      type-Prop (ρ f) → type-Prop (ρ g)) →
    {A : UU l1} → (f : A → type-pseudo-cumulative-hierarchy V) →
    simple-prop-recursion-principle-cumulative-hierarchy ρ τ
      ( set-pseudo-cumulative-hierarchy V f) ＝ ρ f
  compute-simple-prop-recursion-principle-cumulative-hierarchy {l2} ρ τ f =
    compute-prop-recursion-principle-cumulative-hierarchy
      ( λ f _ → ρ f) (λ f g e _ _ _ → τ f g e) f (λ _ → raise-Prop l2 unit-Prop)
```

### The membership relationship for the cumulative hierarchy

```agda
  ∈-cumulative-hierarchy-Prop :
    ( type-pseudo-cumulative-hierarchy V) →
    ( type-pseudo-cumulative-hierarchy V) →
    Prop (lsuc l1)
  ∈-cumulative-hierarchy-Prop x =
    simple-prop-recursion-principle-cumulative-hierarchy
      ( λ {A} f → exists-structure-Prop A (λ a → f a ＝ x))
      ( e)
    where
    e :
      {A B : UU l1} (f : A → type-pseudo-cumulative-hierarchy V)
      ( g : B → type-pseudo-cumulative-hierarchy V) →
      ( e : has-smaller-image f g) →
      ( exists-structure A (λ a → f a ＝ x) →
        exists-structure B (λ b → g b ＝ x))
    e {A} {B} f g s =
      map-universal-property-trunc-Prop
        ( exists-structure-Prop B (λ b → g b ＝ x))
        ( λ ( a , p) →
          map-trunc-Prop (λ (b , q) → (b , q ∙ p)) (s a))

  ∈-cumulative-hierarchy :
    ( type-pseudo-cumulative-hierarchy V) →
    ( type-pseudo-cumulative-hierarchy V) →
    UU (lsuc l1)
  ∈-cumulative-hierarchy x y =
    type-Prop (∈-cumulative-hierarchy-Prop x y)

  id-∈-cumulative-hierarchy :
    ( x : type-pseudo-cumulative-hierarchy V) {A : UU l1}
    ( f : A → type-pseudo-cumulative-hierarchy V) →
    ( ∈-cumulative-hierarchy x (set-pseudo-cumulative-hierarchy V f)) ＝
      exists-structure A (λ a → f a ＝ x)
  id-∈-cumulative-hierarchy x f =
    ap pr1 (compute-simple-prop-recursion-principle-cumulative-hierarchy _ _ f)

  ∈-cumulative-hierarchy-mere-preimage :
    { x : type-pseudo-cumulative-hierarchy V} →
    { A : UU l1}
    { f : A → type-pseudo-cumulative-hierarchy V} →
    ( ∈-cumulative-hierarchy x (set-pseudo-cumulative-hierarchy V f)) →
    exists-structure A (λ a → f a ＝ x)
  ∈-cumulative-hierarchy-mere-preimage {x} {A} {f} =
    tr id (id-∈-cumulative-hierarchy x f)

  mere-preimage-∈-cumulative-hierarchy :
    { x : type-pseudo-cumulative-hierarchy V} →
    { A : UU l1}
    { f : A → type-pseudo-cumulative-hierarchy V} →
    exists-structure A (λ a → f a ＝ x) →
    ( ∈-cumulative-hierarchy x (set-pseudo-cumulative-hierarchy V f))
  mere-preimage-∈-cumulative-hierarchy {x} {A} {f} =
    tr id (inv (id-∈-cumulative-hierarchy x f))

  is-prop-∈-cumulative-hierarchy :
    ( x : type-pseudo-cumulative-hierarchy V) →
    ( y : type-pseudo-cumulative-hierarchy V) →
    is-prop (∈-cumulative-hierarchy x y)
  is-prop-∈-cumulative-hierarchy x y =
    is-prop-type-Prop (∈-cumulative-hierarchy-Prop x y)
```

### The subset relationship for the cumulative hierarchy

```agda
  ⊆-cumulative-hierarchy :
    ( type-pseudo-cumulative-hierarchy V) →
    ( type-pseudo-cumulative-hierarchy V) →
    UU (lsuc l1)
  ⊆-cumulative-hierarchy x y =
    ( v : type-pseudo-cumulative-hierarchy V) →
    ∈-cumulative-hierarchy v x → ∈-cumulative-hierarchy v y

  is-prop-⊆-cumulative-hierarchy :
    ( x : type-pseudo-cumulative-hierarchy V) →
    ( y : type-pseudo-cumulative-hierarchy V) →
    is-prop (⊆-cumulative-hierarchy x y)
  is-prop-⊆-cumulative-hierarchy x y =
    is-prop-Π ( λ v →
      ( is-prop-Π (λ _ → is-prop-∈-cumulative-hierarchy v y)))

  ⊆-cumulative-hierarchy-has-smaller-image :
    { A B : UU l1}
    ( f : A → type-pseudo-cumulative-hierarchy V)
    ( g : B → type-pseudo-cumulative-hierarchy V) →
    ⊆-cumulative-hierarchy
      ( set-pseudo-cumulative-hierarchy V f)
      ( set-pseudo-cumulative-hierarchy V g) →
    has-smaller-image f g
  ⊆-cumulative-hierarchy-has-smaller-image f g s a =
    ∈-cumulative-hierarchy-mere-preimage
      ( s (f a)
        ( mere-preimage-∈-cumulative-hierarchy
          (unit-trunc-Prop (a , refl))))

  has-smaller-image-⊆-cumulative-hierarchy :
    { A B : UU l1}
    ( f : A → type-pseudo-cumulative-hierarchy V)
    ( g : B → type-pseudo-cumulative-hierarchy V) →
    has-smaller-image f g →
    ⊆-cumulative-hierarchy
      ( set-pseudo-cumulative-hierarchy V f)
      ( set-pseudo-cumulative-hierarchy V g)
  has-smaller-image-⊆-cumulative-hierarchy {A} {B} f g s x m =
    mere-preimage-∈-cumulative-hierarchy
      ( map-universal-property-trunc-Prop
        ( exists-structure-Prop B (λ b → g b ＝ x))
        ( λ (a , p) →
          map-trunc-Prop (λ (b , q) → (b , q ∙ p)) (s a))
        ( ∈-cumulative-hierarchy-mere-preimage m))
```

### Extensionality of the membership relation

```agda
  pre-extensionality-∈-cumulative-hierarchy :
    { A : UU l1}
    ( f : A → type-pseudo-cumulative-hierarchy V)
    ( x : type-pseudo-cumulative-hierarchy V) →
    ( ⊆-cumulative-hierarchy x (set-pseudo-cumulative-hierarchy V f)) →
    ( ⊆-cumulative-hierarchy (set-pseudo-cumulative-hierarchy V f) x) →
    x ＝ (set-pseudo-cumulative-hierarchy V f)
  pre-extensionality-∈-cumulative-hierarchy f =
    prop-ind-principle-cumulative-hierarchy
      ( λ x →
        ⊆-cumulative-hierarchy x (set-pseudo-cumulative-hierarchy V f) →
        ⊆-cumulative-hierarchy (set-pseudo-cumulative-hierarchy V f) x →
        x ＝ (set-pseudo-cumulative-hierarchy V f))
      ( λ v →
        is-prop-Π (λ _ →
          is-prop-Π (λ _ →
            is-set-pseudo-cumulative-hierarchy V
              v (set-pseudo-cumulative-hierarchy V f))))
      ( λ g H H₁ H₂ →
        set-ext-pseudo-cumulative-hierarchy V g f
          ( ⊆-cumulative-hierarchy-has-smaller-image g f H₁ ,
            ⊆-cumulative-hierarchy-has-smaller-image f g H₂))

  extensionality-∈-cumulative-hierarchy :
    ( x y : type-pseudo-cumulative-hierarchy V) →
    ( ⊆-cumulative-hierarchy x y) →
    ( ⊆-cumulative-hierarchy y x) →
    x ＝ y
  extensionality-∈-cumulative-hierarchy x =
    prop-ind-principle-cumulative-hierarchy
      ( λ y →
        ⊆-cumulative-hierarchy x y →
        ⊆-cumulative-hierarchy y x → x ＝ y)
      ( λ v →
        is-prop-Π (λ _ →
          is-prop-Π (λ _ →
            is-set-pseudo-cumulative-hierarchy V x v)))
      ( λ f H H₁ H₂ →
        pre-extensionality-∈-cumulative-hierarchy
          f x H₁ H₂)
```

### Cumulative hierarchies satisfy the empty set axiom

```agda
  empty-set-axiom-cumulative-hierarchy :
    ( x : type-pseudo-cumulative-hierarchy V) →
    ¬ (∈-cumulative-hierarchy x empty-set-cumulative-hierarchy)
  empty-set-axiom-cumulative-hierarchy x H =
    map-universal-property-trunc-Prop empty-Prop
      ( λ (z , p) → raise-ex-falso l1 z)
      ( ∈-cumulative-hierarchy-mere-preimage H)
```

### Cumulative hierarchies satisfy the pair axiom

```agda
  pair-cumulative-hierarchy :
    ( x y : type-pseudo-cumulative-hierarchy V) →
    type-pseudo-cumulative-hierarchy V
  pair-cumulative-hierarchy x y =
    set-pseudo-cumulative-hierarchy V bool-map
    where
    bool-map : raise-bool l1 → type-pseudo-cumulative-hierarchy V
    bool-map (map-raise true) = x
    bool-map (map-raise false) = y

  abstract
    pair-axiom-cumulative-hierarchy :
      ( x y v : type-pseudo-cumulative-hierarchy V) →
      ( ∈-cumulative-hierarchy v (pair-cumulative-hierarchy x y) ↔
        type-trunc-Prop ( (v ＝ x) + (v ＝ y)))
    pr1 (pair-axiom-cumulative-hierarchy x y v) H =
      map-universal-property-trunc-Prop
        ( trunc-Prop ((v ＝ x) + (v ＝ y)))
        ( λ where
          ( map-raise true , p) → unit-trunc-Prop (inl (inv p))
          ( map-raise false , p) → unit-trunc-Prop (inr (inv p)))
        ( ∈-cumulative-hierarchy-mere-preimage H)
    pr2 (pair-axiom-cumulative-hierarchy x y v) H =
      mere-preimage-∈-cumulative-hierarchy
        ( map-trunc-Prop
          ( λ where
            ( inl p) → (map-raise true , inv p)
            ( inr p) → (map-raise false , inv p))
          ( H))
```

### Singleton function

```agda
  singleton-cumulative-hierarchy :
    type-pseudo-cumulative-hierarchy V →
    type-pseudo-cumulative-hierarchy V
  singleton-cumulative-hierarchy x =
    ( set-pseudo-cumulative-hierarchy V {raise-unit l1}
      ( λ _ → x))
```

### Cumulative hierarchies satisfy the infinity axiom

```agda
  infinity-cumulative-hierarchy : type-pseudo-cumulative-hierarchy V
  infinity-cumulative-hierarchy =
    set-pseudo-cumulative-hierarchy V ℕ-map
    where
    ℕ-map : raise l1 ℕ → type-pseudo-cumulative-hierarchy V
    ℕ-map (map-raise zero-ℕ) = empty-set-cumulative-hierarchy
    ℕ-map (map-raise (succ-ℕ x)) =
      pair-cumulative-hierarchy
        ( ℕ-map (map-raise x))
        ( singleton-cumulative-hierarchy (ℕ-map (map-raise x)))

  abstract
    infinity-axiom-cumulative-hierarchy :
      ( ∈-cumulative-hierarchy
          empty-set-cumulative-hierarchy
          infinity-cumulative-hierarchy) ×
      ( ( x : type-pseudo-cumulative-hierarchy V) →
        ∈-cumulative-hierarchy x infinity-cumulative-hierarchy →
        ∈-cumulative-hierarchy
          ( pair-cumulative-hierarchy x
            ( singleton-cumulative-hierarchy x))
          ( infinity-cumulative-hierarchy))
    pr1 infinity-axiom-cumulative-hierarchy =
      mere-preimage-∈-cumulative-hierarchy
        ( unit-trunc-Prop (map-raise zero-ℕ , refl))
    pr2 infinity-axiom-cumulative-hierarchy x H =
      mere-preimage-∈-cumulative-hierarchy
        ( map-trunc-Prop
          ( λ where ((map-raise n) , refl) → (map-raise (succ-ℕ n) , refl))
          ( ∈-cumulative-hierarchy-mere-preimage H))
```

### Cumulative hierarchies satisfy the ∈-induction axiom

```agda
  ∈-induction-cumulative-hierarchy :
    {l2 : Level}
    ( P : type-pseudo-cumulative-hierarchy V → UU l2) →
    ( ( x : type-pseudo-cumulative-hierarchy V) → is-prop (P x)) →
    ( ( x : type-pseudo-cumulative-hierarchy V) →
      ( ( y : type-pseudo-cumulative-hierarchy V) →
        ∈-cumulative-hierarchy y x → P y) →
      P x) →
    ( x : type-pseudo-cumulative-hierarchy V) → P x
  ∈-induction-cumulative-hierarchy P P-prop h =
    prop-ind-principle-cumulative-hierarchy P P-prop
      ( λ f IH →
        h (set-pseudo-cumulative-hierarchy V f)
          ( λ y m →
            map-universal-property-trunc-Prop
              ( P y , P-prop y)
              ( λ (a , p) → tr P p (IH a))
              ( ∈-cumulative-hierarchy-mere-preimage m)))
```

### Cumulative hierarchies satisfy the replacement axiom

```agda
  abstract
    replacement-cumulative-hierarchy :
      ( x : type-pseudo-cumulative-hierarchy V) →
      ( r : type-pseudo-cumulative-hierarchy V →
        type-pseudo-cumulative-hierarchy V) →
      exists-structure
        ( type-pseudo-cumulative-hierarchy V)
        ( λ v →
          ( y : type-pseudo-cumulative-hierarchy V) →
          ∈-cumulative-hierarchy y v ↔
          exists-structure
            ( type-pseudo-cumulative-hierarchy V)
            ( λ z → (∈-cumulative-hierarchy z x) × (y ＝ r z)))
    replacement-cumulative-hierarchy x r =
      map-universal-property-trunc-Prop
        ( exists-structure-Prop (type-pseudo-cumulative-hierarchy V) _)
        ( λ where
          ( A , f , refl) →
            unit-trunc-Prop
              ( ( set-pseudo-cumulative-hierarchy V (r ∘ f)) ,
                ( λ y →
                  ( pair
                    ( λ H →
                      map-trunc-Prop
                        ( λ where
                          ( a , refl) →
                            (f a) ,
                            ( mere-preimage-∈-cumulative-hierarchy
                              ( unit-trunc-Prop (a , refl))) ,
                            ( refl))
                        ( ∈-cumulative-hierarchy-mere-preimage H))
                    ( λ H →
                      mere-preimage-∈-cumulative-hierarchy
                        ( map-universal-property-trunc-Prop
                          ( exists-structure-Prop A _)
                          ( λ where
                            ( z , K , refl) →
                              map-trunc-Prop
                                ( λ where (a , refl) → (a , refl))
                                ( ∈-cumulative-hierarchy-mere-preimage K))
                          ( H)))))))
        ( underlying-function-cumulative-hierarchy x)
```

## References

{{#bibliography}} {{#reference UF13}} {{#reference dJKFX23}}
