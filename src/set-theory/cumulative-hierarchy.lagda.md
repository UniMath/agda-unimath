# Cumulative hierarchy

```agda
module set-theory.cumulative-hierarchy where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equational-reasoning
open import foundation.existential-quantification
open import foundation.functoriality-propositional-truncation
open import foundation.identity-types
open import foundation.propositional-extensionality
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.sets
open import foundation.transport
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.equivalences

open import orthogonal-factorization-systems.lifts-of-maps
```

</details>

## Idea

The cumulative hierarchy is a model of set theory.
Instead of introducing it as a HIT, as in the HoTT Book [1, §10.5], we introduce
its induction principle, following [2].

## Definitions

### Pseudo cumulative hierarchy

A type is a pseudo cumulative hierarchy if it has the structure of a cumulative hierarchy, but not necessarily its induction principle.

```agda
has-cumulative-hierarchy-structure :
  {l : Level} → (V : UU (lsuc l)) → UU (lsuc l)
has-cumulative-hierarchy-structure {l} V =
  ( is-set V) ×
    ( Σ ({A : UU l} → (A → V) → V)
      ( λ V-set →
        ( {A B : UU l} (f : A → V) (g : B → V) →
          ( type-trunc-Prop (lift f g) ×
            type-trunc-Prop (lift g f)) → V-set f ＝ V-set g)))

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
    ( type-trunc-Prop (lift f g) × type-trunc-Prop (lift g f)) →
    set-pseudo-cumulative-hierarchy f ＝ set-pseudo-cumulative-hierarchy g
  set-ext-pseudo-cumulative-hierarchy = pr2 (pr2 (pr2 V))
```

### The induction principle of the cumulative hierarchy together with its computation rule.

```agda
module _
  {l1 : Level} (l2 : Level) (V : pseudo-cumulative-hierarchy l1)
  where
  induction-principle-cumulative-hierarchy : UU (lsuc (l1 ⊔ l2))
  induction-principle-cumulative-hierarchy =
    ( P : type-pseudo-cumulative-hierarchy V → UU l2) →
    ( (x : type-pseudo-cumulative-hierarchy V) → is-set (P x)) →
    ( ρ :
      { A : UU l1} (f : A → type-pseudo-cumulative-hierarchy V ) →
      ( (a : A) → P (f a)) → P (set-pseudo-cumulative-hierarchy V f)) →
    ( { A B : UU l1} (f : A → type-pseudo-cumulative-hierarchy V) →
      ( g : B → type-pseudo-cumulative-hierarchy V)
      ( e : type-trunc-Prop (lift f g) × type-trunc-Prop (lift g f))
      ( IH₁ : (a : A) → P (f a))
      ( IH₂ : (b : B) → P (g b)) →
      ( (a : A) → ∃ B (λ b → Σ (f a ＝ g b)
        ( λ p → tr P p (IH₁ a) ＝ IH₂ b))) →
      ( (b : B) → ∃ A (λ a → Σ (g b ＝ f a)
                       (λ p → tr P p (IH₂ b) ＝ IH₁ a))) →
      tr P (set-ext-pseudo-cumulative-hierarchy V f g e) (ρ f IH₁) ＝ ρ g IH₂) →
    (x : type-pseudo-cumulative-hierarchy V) → P x

  compute-induction-principle-cumulative-hierarchy :
    induction-principle-cumulative-hierarchy → UU (lsuc (l1 ⊔ l2))
  compute-induction-principle-cumulative-hierarchy IP =
    ( P : type-pseudo-cumulative-hierarchy V → UU l2) →
    ( σ : (x : type-pseudo-cumulative-hierarchy V) → is-set (P x)) →
    ( ρ :
      { A : UU l1} (f : A → type-pseudo-cumulative-hierarchy V ) →
      ( (a : A) → P (f a)) → P (set-pseudo-cumulative-hierarchy V f)) →
    ( τ :
      { A B : UU l1} (f : A → type-pseudo-cumulative-hierarchy V) →
      ( g : B → type-pseudo-cumulative-hierarchy V)
      ( e : type-trunc-Prop (lift f g) × type-trunc-Prop (lift g f))
      ( IH₁ : (a : A) → P (f a))
      ( IH₂ : (b : B) → P (g b)) →
      ( (a : A) → ∃ B (λ b → Σ (f a ＝ g b)
        ( λ p → tr P p (IH₁ a) ＝ IH₂ b))) →
      ( (b : B) → ∃ A (λ a → Σ (g b ＝ f a)
        (λ p → tr P p (IH₂ b) ＝ IH₁ a))) →
      tr P (set-ext-pseudo-cumulative-hierarchy V f g e) (ρ f IH₁) ＝ ρ g IH₂) →
    { A : UU l1} (f : A → type-pseudo-cumulative-hierarchy V)
    ( IH : (a : A) → P (f a)) →
    IP P σ ρ τ (set-pseudo-cumulative-hierarchy V f) ＝ ρ f IH
```

## Properties

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

### Every element of the cumulative hierarchy is given by a function into the cumulative hierarchy.

```agda
  underlying-function-cumulative-hierarchy :
    { l2 : Level}
    (v : type-pseudo-cumulative-hierarchy V) →
    ∃ ( UU l1)
      ( λ A →
        Σ ( A → type-pseudo-cumulative-hierarchy V)
          ( λ f → set-pseudo-cumulative-hierarchy V f ＝ v))
  underlying-function-cumulative-hierarchy {l2} =
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

### The recursion principle of the cumulative hierarchy together with its computation rule.

```agda
  recursion-principle-cumulative-hierarchy :
    { l2 : Level}
    ( X : UU l2) (σ : is-set X)
    ( ρ : {A : UU l1} → (A → type-pseudo-cumulative-hierarchy V) → (A → X) → X)
    ( τ :
      { A B : UU l1} (f : A → type-pseudo-cumulative-hierarchy V)
      ( g : B → type-pseudo-cumulative-hierarchy V)
      ( e : type-trunc-Prop (lift f g) × type-trunc-Prop (lift g f))
      ( IH₁ : A → X)
      ( IH₂ : B → X) →
      ( (a : A) → ∃ B (λ b → (f a ＝ g b) × (IH₁ a ＝ IH₂ b))) →
      ( (b : B) → ∃ A (λ a → (g b ＝ f a) × (IH₂ b ＝ IH₁ a))) →
      ρ f IH₁ ＝ ρ g IH₂) →
    type-pseudo-cumulative-hierarchy V → X
  recursion-principle-cumulative-hierarchy {l2} X σ ρ τ =
    induction-principle-cumulative-hierarchy-V l2 (λ _ → X) (λ _ → σ) ρ τ'
    where
    τ' :
      { A B : UU l1} (f : A → pr1 V) (g : B → pr1 V)
      ( e : type-trunc-Prop (lift f g) × type-trunc-Prop (lift g f))
      ( IH₁ : (a : A) → X) (IH₂ : (b : B) → X) →
      ( (a : A) → ∃ B (λ b → Σ (f a ＝ g b)
        (λ p → tr (λ _ → X) p (IH₁ a) ＝ IH₂ b))) →
      ( (b : B) → ∃ A (λ a → Σ (g b ＝ f a)
        (λ p → tr (λ _ → X) p (IH₂ b) ＝ IH₁ a))) →
      tr (λ _ → X) (pr2 (pr2 (pr2 V)) f g e) (ρ f IH₁) ＝ ρ g IH₂
    τ' {A} {B} f g e IH₁ IH₂ hIH₁ hIH₂ =
      equational-reasoning
      tr (λ _ → X) (pr2 (pr2 (pr2 V)) f g e) (ρ f IH₁)
        ＝ ρ f IH₁ by tr-const path-f-g (ρ f IH₁)
        ＝ ρ g IH₂ by τ f g e IH₁ IH₂ hIH₁' hIH₂'
      where
      path-f-g :
        set-pseudo-cumulative-hierarchy V f
          ＝ set-pseudo-cumulative-hierarchy V g
      path-f-g = set-ext-pseudo-cumulative-hierarchy V f g e
      hIH₁' : (a : A) → ∃ B (λ b → Σ (f a ＝ g b) (λ _ → IH₁ a ＝ IH₂ b))
      hIH₁' a = map-trunc-Prop
        (λ (b , p , q) → (b , p , (inv (tr-const p _) ∙ q))) (hIH₁ a)
      hIH₂' : (b : B) → ∃ A (λ a → Σ (g b ＝ f a) (λ _ → IH₂ b ＝ IH₁ a))
      hIH₂' b = map-trunc-Prop
        (λ (a , p , q) → (a , p , (inv (tr-const p _) ∙ q))) (hIH₂ b)

  compute-recursion-principle-cumulative-hierarchy :
    { l2 : Level} ( X : UU l2) (σ : is-set X)
    ( ρ : {A : UU l1} → (A → type-pseudo-cumulative-hierarchy V) → (A → X) → X)
    ( τ :
      { A B : UU l1} (f : A → type-pseudo-cumulative-hierarchy V)
      ( g : B → type-pseudo-cumulative-hierarchy V)
      ( e : type-trunc-Prop (lift f g) × type-trunc-Prop (lift g f))
      ( IH₁ : A → X)
      ( IH₂ : B → X) →
      ( ( a : A) → ∃ B (λ b → (f a ＝ g b) × (IH₁ a ＝ IH₂ b))) →
      ( ( b : B) → ∃ A (λ a → (g b ＝ f a) × (IH₂ b ＝ IH₁ a))) →
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
      ( e : type-trunc-Prop (lift f g) × type-trunc-Prop (lift g f))
      ( IH₁ : (a : A) → X) (IH₂ : (b : B) → X) →
      ( ( a : A) → ∃ B (λ b → Σ (f a ＝ g b)
        ( λ p → tr (λ _ → X) p (IH₁ a) ＝ IH₂ b))) →
      ( ( b : B) → ∃ A (λ a → Σ (g b ＝ f a)
        ( λ p → tr (λ _ → X) p (IH₂ b) ＝ IH₁ a))) →
      tr (λ _ → X) (pr2 (pr2 (pr2 V)) f g e) (ρ f IH₁) ＝ ρ g IH₂
    τ' {A} {B} f g e IH₁ IH₂ hIH₁ hIH₂ =
      equational-reasoning
      tr (λ _ → X) (pr2 (pr2 (pr2 V)) f g e) (ρ f IH₁)
        ＝ ρ f IH₁ by tr-const path-f-g (ρ f IH₁)
        ＝ ρ g IH₂ by τ f g e IH₁ IH₂ hIH₁' hIH₂'
      where
      path-f-g :
        set-pseudo-cumulative-hierarchy V f
          ＝ set-pseudo-cumulative-hierarchy V g
      path-f-g = set-ext-pseudo-cumulative-hierarchy V f g e
      hIH₁' : (a : A) → ∃ B (λ b → Σ (f a ＝ g b) (λ _ → IH₁ a ＝ IH₂ b))
      hIH₁' a = map-trunc-Prop
        ( λ (b , p , q) → (b , p , (inv (tr-const p _) ∙ q))) (hIH₁ a)
      hIH₂' : (b : B) → ∃ A (λ a → Σ (g b ＝ f a) (λ _ → IH₂ b ＝ IH₁ a))
      hIH₂' b = map-trunc-Prop
        ( λ (a , p , q) → (a , p , (inv (tr-const p _) ∙ q))) (hIH₂ b)
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
      ( e : type-trunc-Prop (lift g f))
      ( IH₁ : A → Prop l2)
      ( IH₂ : B → Prop l2) →
      ( (a : A) → ∃ B (λ b → (f a ＝ g b) × (IH₁ a ＝ IH₂ b))) →
      type-Prop (ρ f IH₁) → type-Prop (ρ g IH₂)) →
    type-pseudo-cumulative-hierarchy V → Prop l2
  prop-recursion-principle-cumulative-hierarchy {l2} ρ τ =
    recursion-principle-cumulative-hierarchy (Prop l2)
      is-set-type-Prop ρ τ'
    where
    τ' :
      { A B : UU l1} (f : A → type-pseudo-cumulative-hierarchy V)
      ( g : B → type-pseudo-cumulative-hierarchy V) →
      ( type-trunc-Prop (lift f g) × type-trunc-Prop (lift g f)) →
      ( IH₁ : A → Prop l2) (IH₂ : B → Prop l2) →
      ( (a : A) → ∃ B (λ b → (f a ＝ g b) × (IH₁ a ＝ IH₂ b))) →
      ( (b : B) → ∃ A (λ a → (g b ＝ f a) × (IH₂ b ＝ IH₁ a))) →
      ρ f IH₁ ＝ ρ g IH₂
    τ' f g (e₁ , e₂) IH₁ IH₂ hIH₁ hIH₂ =
      eq-iff (τ f g e₂ IH₁ IH₂ hIH₁) (τ g f e₁ IH₂ IH₁ hIH₂)

  compute-prop-recursion-principle-cumulative-hierarchy :
    {l2 : Level}
    ( ρ :
      { A : UU l1} → (A → type-pseudo-cumulative-hierarchy V) →
      ( A → Prop l2) → Prop l2)
    ( τ :
      { A B : UU l1} (f : A → type-pseudo-cumulative-hierarchy V)
      ( g : B → type-pseudo-cumulative-hierarchy V)
      ( e : type-trunc-Prop (lift g f))
      ( IH₁ : A → Prop l2)
      ( IH₂ : B → Prop l2) →
      ( (a : A) → ∃ B (λ b → (f a ＝ g b) × (IH₁ a ＝ IH₂ b))) →
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
      ( type-trunc-Prop (lift f g) × type-trunc-Prop (lift g f)) →
      ( IH₁ : A → Prop l2) (IH₂ : B → Prop l2) →
      ( (a : A) → ∃ B (λ b → (f a ＝ g b) × (IH₁ a ＝ IH₂ b))) →
      ( (b : B) → ∃ A (λ a → (g b ＝ f a) × (IH₂ b ＝ IH₁ a))) →
      ρ f IH₁ ＝ ρ g IH₂
    τ' f g (e₁ , e₂) IH₁ IH₂ hIH₁ hIH₂ =
      eq-iff (τ f g e₂ IH₁ IH₂ hIH₁) (τ g f e₁ IH₂ IH₁ hIH₂)
```

Another simplification of the recursion principle, when recursive calls are not needed.

```agda
  simple-prop-recursion-principle-cumulative-hierarchy :
    {l2 : Level}
    ( ρ : {A : UU l1} → (A → type-pseudo-cumulative-hierarchy V) → Prop l2)
    ( τ :
      { A B : UU l1} (f : A → type-pseudo-cumulative-hierarchy V)
      ( g : B → type-pseudo-cumulative-hierarchy V) →
      ( type-trunc-Prop (lift g f)) → type-Prop (ρ f) → type-Prop (ρ g)) →
    type-pseudo-cumulative-hierarchy V → Prop l2
  simple-prop-recursion-principle-cumulative-hierarchy {l2} ρ τ =
    prop-recursion-principle-cumulative-hierarchy
      ( λ f _ → ρ f) (λ f g e _ _ _ → τ f g e)

  compute-simple-prop-recursion-principle-cumulative-hierarchy : {l2 : Level}
    ( ρ : {A : UU l1} → (A → type-pseudo-cumulative-hierarchy V) → Prop l2)
    ( τ :
      { A B : UU l1} (f : A → type-pseudo-cumulative-hierarchy V)
      ( g : B → type-pseudo-cumulative-hierarchy V) →
      ( type-trunc-Prop (lift g f)) → type-Prop (ρ f) → type-Prop (ρ g)) →
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
      (λ {A} f → (∃ A (λ a → f a ＝ x)) , is-prop-∃ _ _) e
    where
    e :
      {A B : UU l1} (f : A → type-pseudo-cumulative-hierarchy V)
      ( g : B → type-pseudo-cumulative-hierarchy V) →
      ( type-trunc-Prop (lift g f)) →
      ( ∃ A (λ a → f a ＝ x) → ∃ B (λ b → g b ＝ x))
    e {A} {B} f g s =
      map-universal-property-trunc-Prop
        ( ∃-Prop B (λ b → g b ＝ x))
        ( λ (a , p) →
          map-trunc-Prop (λ (h , q) → h a , (inv (q a) ∙ p)) s)

  ∈-cumulative-hierarchy :
    ( type-pseudo-cumulative-hierarchy V) →
    ( type-pseudo-cumulative-hierarchy V) →
    UU (lsuc l1)
  ∈-cumulative-hierarchy x y =
    type-Prop (∈-cumulative-hierarchy-Prop x y)

  id-∈-cumulative-hierarchy :
    ( x : type-pseudo-cumulative-hierarchy V) {A : UU l1}
    ( f : A → type-pseudo-cumulative-hierarchy V) →
    ( ∈-cumulative-hierarchy x (set-pseudo-cumulative-hierarchy V f))
      ＝ ∃ A (λ a → f a ＝ x)
  id-∈-cumulative-hierarchy x f =
    ap pr1 (compute-simple-prop-recursion-principle-cumulative-hierarchy _ _ f)

  is-prop-∈-cumulative-hierarchy :
    ( x : type-pseudo-cumulative-hierarchy V) →
    ( y : type-pseudo-cumulative-hierarchy V) →
    is-prop (∈-cumulative-hierarchy x y)
  is-prop-∈-cumulative-hierarchy x y =
    is-prop-type-Prop (∈-cumulative-hierarchy-Prop x y)
```

-- ### The subset relationship for the cumulative hierarchy

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
```

## References

1. Institute for Advanced Study. Homotopy Type Theory: Univalent Foundations of Mathematics.
2. Tom de Jong, in collaboration with Nicolai Kraus, Fredrik Nordvall Forsberg and Chuangjie Xu. <https://www.cs.bham.ac.uk/~mhe/agda/UF.CumulativeHierarchy.html>
