# Pullbacks

```agda
module foundation-core.pullbacks where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cones-over-cospans
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.families-of-equivalences
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-fibers-of-maps
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.diagonal-maps-of-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.type-theoretic-principle-of-choice
open import foundation-core.universal-property-pullbacks
```

</details>

## Definitions

### The standard pullback of a cospan

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
  where

  standard-pullback : UU (l1 ⊔ l2 ⊔ l3)
  standard-pullback = Σ A (λ x → Σ B (λ y → f x ＝ g y))

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {f : A → X} {g : B → X}
  where

  vertical-map-standard-pullback : standard-pullback f g → A
  vertical-map-standard-pullback = pr1

  horizontal-map-standard-pullback : standard-pullback f g → B
  horizontal-map-standard-pullback t = pr1 (pr2 t)

  coherence-square-standard-pullback :
    ( f ∘ vertical-map-standard-pullback) ~
    ( g ∘ horizontal-map-standard-pullback)
  coherence-square-standard-pullback t = pr2 (pr2 t)
```

### The cone at the standard pullback

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
  where

  cone-standard-pullback : cone f g (standard-pullback f g)
  pr1 cone-standard-pullback = vertical-map-standard-pullback
  pr1 (pr2 cone-standard-pullback) = horizontal-map-standard-pullback
  pr2 (pr2 cone-standard-pullback) = coherence-square-standard-pullback
```

### The gap map into the standard pullback

The **gap map** of a square is the map fron the vertex of the
[cone](foundation.cones-over-cospans.md) into the standard pullback.

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X)
  where

  gap : cone f g C → C → standard-pullback f g
  pr1 (gap c z) = vertical-map-cone f g c z
  pr1 (pr2 (gap c z)) = horizontal-map-cone f g c z
  pr2 (pr2 (gap c z)) = coherence-square-cone f g c z
```

### The property of being a pullback

The [proposition](foundation-core.propositions.md) `is-pullback` is the
assertion that the gap map is an [equivalence](foundation-core.equivalences.md).
Note that this proposition is [small](foundation-core.small-types.md), whereas
[the universal property](foundation-core.universal-property-pullbacks.md) is a
large proposition.

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X)
  where

  is-pullback : cone f g C → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-pullback c = is-equiv (gap f g c)
```

## Properties

### Characterization of the identity type of the standard pullback

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
  where

  Eq-standard-pullback : (t t' : standard-pullback f g) → UU (l1 ⊔ l2 ⊔ l3)
  Eq-standard-pullback (a , b , p) (a' , b' , p') =
    Σ (a ＝ a') (λ α → Σ (b ＝ b') (λ β → ap f α ∙ p' ＝ p ∙ ap g β))

  refl-Eq-standard-pullback :
    (t : standard-pullback f g) → Eq-standard-pullback t t
  pr1 (refl-Eq-standard-pullback (a , b , p)) = refl
  pr1 (pr2 (refl-Eq-standard-pullback (a , b , p))) = refl
  pr2 (pr2 (refl-Eq-standard-pullback (a , b , p))) = inv right-unit

  Eq-eq-standard-pullback :
    (s t : standard-pullback f g) → s ＝ t → Eq-standard-pullback s t
  Eq-eq-standard-pullback s .s refl = refl-Eq-standard-pullback s

  extensionality-standard-pullback :
    (t t' : standard-pullback f g) → (t ＝ t') ≃ Eq-standard-pullback t t'
  extensionality-standard-pullback (a , b , p) =
    extensionality-Σ
      ( λ {a'} bp' α →
        Σ (b ＝ pr1 bp') (λ β → ap f α ∙ pr2 bp' ＝ p ∙ ap g β))
      ( refl)
      ( refl , inv right-unit)
      ( λ x → id-equiv)
      ( extensionality-Σ
        ( λ p' β → p' ＝ p ∙ ap g β)
        ( refl)
        ( inv right-unit)
        ( λ y → id-equiv)
        ( λ p' → equiv-concat' p' (inv right-unit) ∘e equiv-inv p p'))

  map-extensionality-standard-pullback :
    { s t : standard-pullback f g}
    ( α : vertical-map-standard-pullback s ＝ vertical-map-standard-pullback t)
    ( β :
      horizontal-map-standard-pullback s ＝ horizontal-map-standard-pullback t) →
    ( ( ap f α ∙ coherence-square-standard-pullback t) ＝
      ( coherence-square-standard-pullback s ∙ ap g β)) →
    s ＝ t
  map-extensionality-standard-pullback {s} {t} α β γ =
    map-inv-equiv
      ( extensionality-standard-pullback s t)
      ( α , β , γ)
```

### The standard pullback satisfies the universal property of pullbacks

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
  where

  abstract
    universal-property-pullback-standard-pullback :
      {l : Level} →
      universal-property-pullback l f g (cone-standard-pullback f g)
    universal-property-pullback-standard-pullback C =
      is-equiv-comp
        ( tot (λ p → map-distributive-Π-Σ))
        ( mapping-into-Σ)
        ( is-equiv-mapping-into-Σ)
        ( is-equiv-tot-is-fiberwise-equiv
          ( λ p → is-equiv-map-distributive-Π-Σ))
```

### A cone is equal to the value of cone-map at its own gap map

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X)
  where

  htpy-cone-up-pullback-standard-pullback :
    (c : cone f g C) →
    htpy-cone f g (cone-map f g (cone-standard-pullback f g) (gap f g c)) c
  pr1 (htpy-cone-up-pullback-standard-pullback c) = refl-htpy
  pr1 (pr2 (htpy-cone-up-pullback-standard-pullback c)) = refl-htpy
  pr2 (pr2 (htpy-cone-up-pullback-standard-pullback c)) = right-unit-htpy
```

### A cone satisfies the universal property of the pullback if and only if the gap map is an equivalence

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X)
  where

  abstract
    is-pullback-universal-property-pullback :
      (c : cone f g C) →
      ({l : Level} → universal-property-pullback l f g c) → is-pullback f g c
    is-pullback-universal-property-pullback c =
      is-equiv-up-pullback-up-pullback
        ( cone-standard-pullback f g)
        ( c)
        ( gap f g c)
        ( htpy-cone-up-pullback-standard-pullback f g c)
        ( universal-property-pullback-standard-pullback f g)

  abstract
    universal-property-pullback-is-pullback :
      (c : cone f g C) → is-pullback f g c →
      {l : Level} → universal-property-pullback l f g c
    universal-property-pullback-is-pullback c is-pullback-c =
      up-pullback-up-pullback-is-equiv
        ( cone-standard-pullback f g)
        ( c)
        ( gap f g c)
        ( htpy-cone-up-pullback-standard-pullback f g c)
        ( is-pullback-c)
        ( universal-property-pullback-standard-pullback f g)
```

### The pullback of a Σ-type

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (Q : B → UU l3)
  where

  standard-pullback-Σ : UU (l1 ⊔ l3)
  standard-pullback-Σ = Σ A (λ x → Q (f x))

  cone-standard-pullback-Σ : cone f pr1 standard-pullback-Σ
  pr1 cone-standard-pullback-Σ = pr1
  pr1 (pr2 cone-standard-pullback-Σ) = map-Σ-map-base f Q
  pr2 (pr2 cone-standard-pullback-Σ) = refl-htpy

  inv-gap-cone-standard-pullback-Σ :
    standard-pullback f (pr1 {B = Q}) → standard-pullback-Σ
  pr1 (inv-gap-cone-standard-pullback-Σ (x , (.(f x) , q) , refl)) = x
  pr2 (inv-gap-cone-standard-pullback-Σ (x , (.(f x) , q) , refl)) = q

  abstract
    is-section-inv-gap-cone-standard-pullback-Σ :
      ( gap f pr1 cone-standard-pullback-Σ ∘ inv-gap-cone-standard-pullback-Σ) ~
      ( id)
    is-section-inv-gap-cone-standard-pullback-Σ (x , (.(f x) , q) , refl) =
      refl

  abstract
    is-retraction-inv-gap-cone-standard-pullback-Σ :
      ( inv-gap-cone-standard-pullback-Σ ∘
        gap f pr1 cone-standard-pullback-Σ) ~ id
    is-retraction-inv-gap-cone-standard-pullback-Σ (x , q) = refl

  abstract
    is-pullback-cone-standard-pullback-Σ :
      is-pullback f pr1 cone-standard-pullback-Σ
    is-pullback-cone-standard-pullback-Σ =
      is-equiv-is-invertible
        inv-gap-cone-standard-pullback-Σ
        is-section-inv-gap-cone-standard-pullback-Σ
        is-retraction-inv-gap-cone-standard-pullback-Σ

  compute-standard-pullback-Σ :
    standard-pullback-Σ ≃ standard-pullback f pr1
  pr1 compute-standard-pullback-Σ = gap f pr1 cone-standard-pullback-Σ
  pr2 compute-standard-pullback-Σ = is-pullback-cone-standard-pullback-Σ
```

### Pullbacks are symmetric

```agda
map-commutative-standard-pullback :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) → standard-pullback f g → standard-pullback g f
pr1 (map-commutative-standard-pullback f g x) =
  horizontal-map-standard-pullback x
pr1 (pr2 (map-commutative-standard-pullback f g x)) =
  vertical-map-standard-pullback x
pr2 (pr2 (map-commutative-standard-pullback f g x)) =
  inv (coherence-square-standard-pullback x)

inv-inv-map-commutative-standard-pullback :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) →
  ( map-commutative-standard-pullback f g ∘
    map-commutative-standard-pullback g f) ~ id
inv-inv-map-commutative-standard-pullback f g x =
  eq-pair-eq-pr2
    ( eq-pair-eq-pr2
      ( inv-inv (coherence-square-standard-pullback x)))

abstract
  is-equiv-map-commutative-standard-pullback :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
    (f : A → X) (g : B → X) → is-equiv (map-commutative-standard-pullback f g)
  is-equiv-map-commutative-standard-pullback f g =
    is-equiv-is-invertible
      ( map-commutative-standard-pullback g f)
      ( inv-inv-map-commutative-standard-pullback f g)
      ( inv-inv-map-commutative-standard-pullback g f)

commutative-standard-pullback :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) →
  standard-pullback f g ≃ standard-pullback g f
pr1 (commutative-standard-pullback f g) =
  map-commutative-standard-pullback f g
pr2 (commutative-standard-pullback f g) =
  is-equiv-map-commutative-standard-pullback f g

triangle-map-commutative-standard-pullback :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c : cone f g C) →
  ( gap g f (swap-cone f g c)) ~
  ( map-commutative-standard-pullback f g ∘ gap f g c)
triangle-map-commutative-standard-pullback f g (p , q , H) x = refl

abstract
  is-pullback-swap-cone :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) (g : B → X) (c : cone f g C) →
    is-pullback f g c → is-pullback g f (swap-cone f g c)
  is-pullback-swap-cone f g c is-pb-c =
    is-equiv-left-map-triangle
      ( gap g f (swap-cone f g c))
      ( map-commutative-standard-pullback f g)
      ( gap f g c)
      ( triangle-map-commutative-standard-pullback f g c)
      ( is-pb-c)
      ( is-equiv-map-commutative-standard-pullback f g)

abstract
  is-pullback-swap-cone' :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) (g : B → X) (c : cone f g C) →
    is-pullback g f (swap-cone f g c) → is-pullback f g c
  is-pullback-swap-cone' f g c is-pb-c' =
    is-equiv-top-map-triangle
      ( gap g f (swap-cone f g c))
      ( map-commutative-standard-pullback f g)
      ( gap f g c)
      ( triangle-map-commutative-standard-pullback f g c)
      ( is-equiv-map-commutative-standard-pullback f g)
      ( is-pb-c')
```

### Pullbacks can be "folded"

```agda
fold-cone :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) →
  cone f g C → cone (map-prod f g) (diagonal X) C
pr1 (pr1 (fold-cone f g c) z) = vertical-map-cone f g c z
pr2 (pr1 (fold-cone f g c) z) = horizontal-map-cone f g c z
pr1 (pr2 (fold-cone f g c)) = g ∘ horizontal-map-cone f g c
pr2 (pr2 (fold-cone f g c)) z = eq-pair (coherence-square-cone f g c z) refl

map-fold-cone :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) → (g : B → X) →
  standard-pullback f g → standard-pullback (map-prod f g) (diagonal X)
pr1 (pr1 (map-fold-cone f g x)) = vertical-map-standard-pullback x
pr2 (pr1 (map-fold-cone f g x)) = horizontal-map-standard-pullback x
pr1 (pr2 (map-fold-cone f g x)) = g (horizontal-map-standard-pullback x)
pr2 (pr2 (map-fold-cone f g x)) =
  eq-pair (coherence-square-standard-pullback x) refl

inv-map-fold-cone :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) → (g : B → X) →
  standard-pullback (map-prod f g) (diagonal X) → standard-pullback f g
pr1 (inv-map-fold-cone f g ((a , b) , x , α)) = a
pr1 (pr2 (inv-map-fold-cone f g ((a , b) , x , α))) = b
pr2 (pr2 (inv-map-fold-cone f g ((a , b) , x , α))) = ap pr1 α ∙ inv (ap pr2 α)

abstract
  is-section-inv-map-fold-cone :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
    (f : A → X) (g : B → X) →
    ((map-fold-cone f g) ∘ (inv-map-fold-cone f g)) ~ id
  is-section-inv-map-fold-cone {A = A} {B} {X} f g ((a , b) , (x , α)) =
    map-extensionality-standard-pullback
      ( map-prod f g)
      ( diagonal X)
      refl
      ( ap pr2 α)
      ( ( inv (is-section-pair-eq α)) ∙
        ( ap
          ( λ t → eq-pair t (ap pr2 α))
          ( ( inv right-unit) ∙
            ( inv (ap (concat (ap pr1 α) x) (left-inv (ap pr2 α)))) ∙
            ( inv (assoc (ap pr1 α) (inv (ap pr2 α)) (ap pr2 α))))) ∙
        ( eq-pair-concat
          ( ap pr1 α ∙ inv (ap pr2 α))
          ( ap pr2 α)
          ( refl)
          ( ap pr2 α)) ∙
        ( ap
          ( concat
            ( eq-pair (ap pr1 α ∙ inv (ap pr2 α)) refl)
            ( x , x))
          ( inv (ap-diagonal (ap pr2 α)))))

abstract
  is-retraction-inv-map-fold-cone :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
    (f : A → X) (g : B → X) →
    inv-map-fold-cone f g ∘ map-fold-cone f g ~ id
  is-retraction-inv-map-fold-cone f g (a , b , p) =
    map-extensionality-standard-pullback f g
      ( refl)
      ( refl)
      ( inv
        ( ( ap
            ( concat' (f a) refl)
            ( ( ap
                ( λ t → t ∙ inv (ap pr2 (eq-pair p refl)))
                ( ap-pr1-eq-pair p refl)) ∙
              ( ap (λ t → p ∙ inv t) (ap-pr2-eq-pair p refl)) ∙
              ( right-unit))) ∙
          ( right-unit)))

abstract
  is-equiv-map-fold-cone :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
    (f : A → X) (g : B → X) → is-equiv (map-fold-cone f g)
  is-equiv-map-fold-cone f g =
    is-equiv-is-invertible
      ( inv-map-fold-cone f g)
      ( is-section-inv-map-fold-cone f g)
      ( is-retraction-inv-map-fold-cone f g)

triangle-map-fold-cone :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c : cone f g C) →
  ( gap (map-prod f g) (diagonal X) (fold-cone f g c)) ~
  ( map-fold-cone f g ∘ gap f g c)
triangle-map-fold-cone f g c z = refl

abstract
  is-pullback-fold-cone-is-pullback :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) (g : B → X) (c : cone f g C) →
    is-pullback f g c →
    is-pullback (map-prod f g) (diagonal X) (fold-cone f g c)
  is-pullback-fold-cone-is-pullback {X = X} f g c is-pb-c =
    is-equiv-left-map-triangle
      ( gap (map-prod f g) (diagonal X) (fold-cone f g c))
      ( map-fold-cone f g)
      ( gap f g c)
      ( triangle-map-fold-cone f g c)
      ( is-pb-c)
      ( is-equiv-map-fold-cone f g)

abstract
  is-pullback-is-pullback-fold-cone :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) (g : B → X) (c : cone f g C) →
    is-pullback (map-prod f g) (diagonal X) (fold-cone f g c) →
    is-pullback f g c
  is-pullback-is-pullback-fold-cone {X = X} f g c is-pb-fold =
    is-equiv-top-map-triangle
      ( gap (map-prod f g) (diagonal X) (fold-cone f g c))
      ( map-fold-cone f g)
      ( gap f g c)
      ( triangle-map-fold-cone f g c)
      ( is-equiv-map-fold-cone f g)
      ( is-pb-fold)
```

### Products of pullbacks are pullbacks

```agda
prod-cone :
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} {C' : UU l4'}
  (f : A → X) (g : B → X) (f' : A' → X') (g' : B' → X') →
  cone f g C → cone f' g' C' →
  cone (map-prod f f') (map-prod g g') (C × C')
pr1 (prod-cone f g f' g' (p , q , H) (p' , q' , H')) = map-prod p p'
pr1 (pr2 (prod-cone f g f' g' (p , q , H) (p' , q' , H'))) = map-prod q q'
pr2 (pr2 (prod-cone f g f' g' (p , q , H) (p' , q' , H'))) =
  ( inv-htpy (map-prod-comp p p' f f')) ∙h
  ( htpy-map-prod H H') ∙h
  ( map-prod-comp q q' g g')

map-prod-cone :
  {l1 l2 l3 l1' l2' l3' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3}
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'}
  (f : A → X) (g : B → X) (f' : A' → X') (g' : B' → X') →
  (standard-pullback f g) × (standard-pullback f' g') →
  standard-pullback (map-prod f f') (map-prod g g')
map-prod-cone {A' = A'} {B'} f g f' g' =
  ( tot
    ( λ t →
      ( tot (λ s → eq-pair')) ∘
      ( map-interchange-Σ-Σ (λ y p y' → f' (pr2 t) ＝ g' y')))) ∘
  ( map-interchange-Σ-Σ (λ x t x' → Σ B' (λ y' → f' x' ＝ g' y')))

triangle-map-prod-cone :
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} {C' : UU l4'}
  (f : A → X) (g : B → X) (c : cone f g C)
  (f' : A' → X') (g' : B' → X') (c' : cone f' g' C') →
  ( gap (map-prod f f') (map-prod g g') (prod-cone f g f' g' c c')) ~
  ( map-prod-cone f g f' g' ∘ map-prod (gap f g c) (gap f' g' c'))
triangle-map-prod-cone f g c f' g' c' z =
  eq-pair-eq-pr2 (eq-pair-eq-pr2 right-unit)

abstract
  is-equiv-map-prod-cone :
    {l1 l2 l3 l1' l2' l3' : Level}
    {A : UU l1} {B : UU l2} {X : UU l3}
    {A' : UU l1'} {B' : UU l2'} {X' : UU l3'}
    (f : A → X) (g : B → X) (f' : A' → X') (g' : B' → X') →
    is-equiv (map-prod-cone f g f' g')
  is-equiv-map-prod-cone f g f' g' =
    is-equiv-comp
      ( tot
        ( λ t →
          ( tot (λ s → eq-pair')) ∘
          ( map-interchange-Σ-Σ _)))
      ( map-interchange-Σ-Σ _)
      ( is-equiv-map-interchange-Σ-Σ _)
      ( is-equiv-tot-is-fiberwise-equiv
        ( λ t →
          is-equiv-comp
            ( tot (λ s → eq-pair'))
            ( map-interchange-Σ-Σ
              ( λ y p y' → f' (pr2 t) ＝ g' y'))
            ( is-equiv-map-interchange-Σ-Σ _)
            ( is-equiv-tot-is-fiberwise-equiv
              ( λ s →
                is-equiv-comp
                  ( eq-pair')
                  ( id)
                  ( is-equiv-id)
                  ( is-equiv-eq-pair
                    ( map-prod f f' t)
                    ( map-prod g g' s))))))

abstract
  is-pullback-prod-is-pullback-pair :
    {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
    {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} {C' : UU l4'}
    (f : A → X) (g : B → X) (c : cone f g C)
    (f' : A' → X') (g' : B' → X') (c' : cone f' g' C') →
    is-pullback f g c → is-pullback f' g' c' →
    is-pullback
      ( map-prod f f') (map-prod g g') (prod-cone f g f' g' c c')
  is-pullback-prod-is-pullback-pair f g c f' g' c' is-pb-c is-pb-c' =
    is-equiv-left-map-triangle
      ( gap (map-prod f f') (map-prod g g') (prod-cone f g f' g' c c'))
      ( map-prod-cone f g f' g')
      ( map-prod (gap f g c) (gap f' g' c'))
      ( triangle-map-prod-cone f g c f' g' c')
      ( is-equiv-map-prod (gap f g c) (gap f' g' c') is-pb-c is-pb-c')
      ( is-equiv-map-prod-cone f g f' g')

abstract
  is-pullback-left-factor-is-pullback-prod :
    {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
    {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} {C' : UU l4'}
    (f : A → X) (g : B → X) (c : cone f g C)
    (f' : A' → X') (g' : B' → X') (c' : cone f' g' C') →
    is-pullback
      ( map-prod f f')
      ( map-prod g g')
      ( prod-cone f g f' g' c c') →
    standard-pullback f' g' → is-pullback f g c
  is-pullback-left-factor-is-pullback-prod f g c f' g' c' is-pb-cc' t =
    is-equiv-left-factor-is-equiv-map-prod (gap f g c) (gap f' g' c') t
      ( is-equiv-top-map-triangle
        ( gap
          ( map-prod f f')
          ( map-prod g g')
          ( prod-cone f g f' g' c c'))
      ( map-prod-cone f g f' g')
        ( map-prod (gap f g c) (gap f' g' c'))
        ( triangle-map-prod-cone f g c f' g' c')
        ( is-equiv-map-prod-cone f g f' g')
        ( is-pb-cc'))

abstract
  is-pullback-right-factor-is-pullback-prod :
    {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
    {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} {C' : UU l4'}
    (f : A → X) (g : B → X) (c : cone f g C)
    (f' : A' → X') (g' : B' → X') (c' : cone f' g' C') →
    is-pullback
      ( map-prod f f')
      ( map-prod g g')
      ( prod-cone f g f' g' c c') →
    standard-pullback f g → is-pullback f' g' c'
  is-pullback-right-factor-is-pullback-prod f g c f' g' c' is-pb-cc' t =
    is-equiv-right-factor-is-equiv-map-prod (gap f g c) (gap f' g' c') t
      ( is-equiv-top-map-triangle
        ( gap
          ( map-prod f f')
          ( map-prod g g')
          ( prod-cone f g f' g' c c'))
        ( map-prod-cone f g f' g')
        ( map-prod (gap f g c) (gap f' g' c'))
        ( triangle-map-prod-cone f g c f' g' c')
        ( is-equiv-map-prod-cone f g f' g')
        ( is-pb-cc'))
```

### A family of maps over a base map induces a pullback square if and only if it is a family of equivalences

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {P : A → UU l3}
  (Q : B → UU l4) (f : A → B) (g : (x : A) → (P x) → (Q (f x)))
  where

  cone-map-Σ : cone f pr1 (Σ A P)
  pr1 cone-map-Σ = pr1
  pr1 (pr2 cone-map-Σ) = map-Σ Q f g
  pr2 (pr2 cone-map-Σ) = refl-htpy

  abstract
    is-pullback-is-fiberwise-equiv :
      is-fiberwise-equiv g → is-pullback f pr1 cone-map-Σ
    is-pullback-is-fiberwise-equiv is-equiv-g =
      is-equiv-comp
        ( gap f pr1 (cone-standard-pullback-Σ f Q))
        ( tot g)
        ( is-equiv-tot-is-fiberwise-equiv is-equiv-g)
        ( is-pullback-cone-standard-pullback-Σ f Q)

  abstract
    universal-property-pullback-is-fiberwise-equiv :
      is-fiberwise-equiv g → {l : Level} →
      universal-property-pullback l f pr1 cone-map-Σ
    universal-property-pullback-is-fiberwise-equiv is-equiv-g =
      universal-property-pullback-is-pullback f pr1 cone-map-Σ
        ( is-pullback-is-fiberwise-equiv is-equiv-g)

  abstract
    is-fiberwise-equiv-is-pullback :
      is-pullback f pr1 cone-map-Σ → is-fiberwise-equiv g
    is-fiberwise-equiv-is-pullback is-pullback-cone-map-Σ =
      is-fiberwise-equiv-is-equiv-tot
        ( is-equiv-right-factor
          ( gap f pr1 (cone-standard-pullback-Σ f Q))
          ( tot g)
          ( is-pullback-cone-standard-pullback-Σ f Q)
          ( is-pullback-cone-map-Σ))

  abstract
    is-fiberwise-equiv-universal-property-pullback :
      ( {l : Level} → universal-property-pullback l f pr1 cone-map-Σ) →
      is-fiberwise-equiv g
    is-fiberwise-equiv-universal-property-pullback up =
      is-fiberwise-equiv-is-pullback
        ( is-pullback-universal-property-pullback f pr1 cone-map-Σ up)
```

### A cone is a pullback if and only if it induces a family of equivalences between the fibers of the vertical maps

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4}
  (f : A → X) (g : B → X) (c : cone f g C)
  where

  square-tot-map-fiber-cone :
    ( gap f g c ∘ map-equiv-total-fiber (pr1 c)) ~
    ( tot (λ a → tot (λ b → inv)) ∘ tot (map-fiber-cone f g c))
  square-tot-map-fiber-cone (.(vertical-map-cone f g c x) , x , refl) =
    eq-pair-eq-pr2
      ( eq-pair-eq-pr2
        ( inv (ap inv right-unit ∙ inv-inv (coherence-square-cone f g c x))))

  abstract
    is-fiberwise-equiv-map-fiber-cone-is-pullback :
      is-pullback f g c → is-fiberwise-equiv (map-fiber-cone f g c)
    is-fiberwise-equiv-map-fiber-cone-is-pullback pb =
      is-fiberwise-equiv-is-equiv-tot
        ( is-equiv-top-is-equiv-bottom-square
          ( map-equiv-total-fiber (vertical-map-cone f g c))
          ( tot (λ x → tot (λ y → inv)))
          ( tot (map-fiber-cone f g c))
          ( gap f g c)
          ( square-tot-map-fiber-cone)
          ( is-equiv-map-equiv-total-fiber (vertical-map-cone f g c))
          ( is-equiv-tot-is-fiberwise-equiv
            ( λ x →
              is-equiv-tot-is-fiberwise-equiv
                ( λ y → is-equiv-inv (g y) (f x))))
          ( pb))

  abstract
    is-pullback-is-fiberwise-equiv-map-fiber-cone :
      is-fiberwise-equiv (map-fiber-cone f g c) → is-pullback f g c
    is-pullback-is-fiberwise-equiv-map-fiber-cone is-equiv-fsq =
      is-equiv-bottom-is-equiv-top-square
        ( map-equiv-total-fiber (vertical-map-cone f g c))
        ( tot (λ x → tot (λ y → inv)))
        ( tot (map-fiber-cone f g c))
        ( gap f g c)
        ( square-tot-map-fiber-cone)
        ( is-equiv-map-equiv-total-fiber (vertical-map-cone f g c))
        ( is-equiv-tot-is-fiberwise-equiv
          ( λ x →
            is-equiv-tot-is-fiberwise-equiv
              ( λ y → is-equiv-inv (g y) (f x))))
        ( is-equiv-tot-is-fiberwise-equiv is-equiv-fsq)
```

### The horizontal pullback pasting property

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  (i : X → Y) (j : Y → Z) (h : C → Z)
  where

  abstract
    is-pullback-rectangle-is-pullback-left-square :
      (c : cone j h B) (d : cone i (vertical-map-cone j h c) A) →
      is-pullback j h c → is-pullback i (vertical-map-cone j h c) d →
      is-pullback (j ∘ i) h (pasting-horizontal-cone i j h c d)
    is-pullback-rectangle-is-pullback-left-square c d is-pb-c is-pb-d =
      is-pullback-is-fiberwise-equiv-map-fiber-cone (j ∘ i) h
        ( pasting-horizontal-cone i j h c d)
        ( λ x →
          is-equiv-left-map-triangle
            ( map-fiber-cone (j ∘ i) h (pasting-horizontal-cone i j h c d) x)
            ( map-fiber-cone j h c (i x))
            ( map-fiber-cone i (vertical-map-cone j h c) d x)
            ( preserves-pasting-horizontal-map-fiber-cone i j h c d x)
            ( is-fiberwise-equiv-map-fiber-cone-is-pullback i
              ( vertical-map-cone j h c)
              ( d)
              ( is-pb-d)
              ( x))
            ( is-fiberwise-equiv-map-fiber-cone-is-pullback j h c is-pb-c
              ( i x)))

  abstract
    is-pullback-left-square-is-pullback-rectangle :
      (c : cone j h B) (d : cone i (vertical-map-cone j h c) A) →
      is-pullback j h c →
      is-pullback (j ∘ i) h (pasting-horizontal-cone i j h c d) →
      is-pullback i (vertical-map-cone j h c) d
    is-pullback-left-square-is-pullback-rectangle c d is-pb-c is-pb-rect =
      is-pullback-is-fiberwise-equiv-map-fiber-cone i
        ( vertical-map-cone j h c)
        ( d)
        ( λ x →
          is-equiv-top-map-triangle
            ( map-fiber-cone (j ∘ i) h (pasting-horizontal-cone i j h c d) x)
            ( map-fiber-cone j h c (i x))
            ( map-fiber-cone i (vertical-map-cone j h c) d x)
            ( preserves-pasting-horizontal-map-fiber-cone i j h c d x)
            ( is-fiberwise-equiv-map-fiber-cone-is-pullback j h c is-pb-c (i x))
            ( is-fiberwise-equiv-map-fiber-cone-is-pullback
              ( j ∘ i)
              ( h)
              ( pasting-horizontal-cone i j h c d)
              ( is-pb-rect)
              ( x)))
```

### The vertical pullback pasting property

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  (f : C → Z) (g : Y → Z) (h : X → Y)
  where

  abstract
    is-pullback-top-is-pullback-rectangle :
      (c : cone f g B) (d : cone (horizontal-map-cone f g c) h A) →
      is-pullback f g c →
      is-pullback f (g ∘ h) (pasting-vertical-cone f g h c d) →
      is-pullback (horizontal-map-cone f g c) h d
    is-pullback-top-is-pullback-rectangle c d is-pb-c is-pb-dc =
      is-pullback-is-fiberwise-equiv-map-fiber-cone
        ( horizontal-map-cone f g c)
        ( h)
        ( d)
        ( λ x →
          is-fiberwise-equiv-is-equiv-map-Σ
            ( λ t → fiber h (pr1 t))
            ( map-fiber-cone f g c (vertical-map-cone f g c x))
            ( λ t → map-fiber-cone (horizontal-map-cone f g c) h d (pr1 t))
            ( is-fiberwise-equiv-map-fiber-cone-is-pullback f g c is-pb-c
              ( vertical-map-cone f g c x))
            ( is-equiv-top-is-equiv-bottom-square
              ( inv-map-compute-fiber-comp
                ( vertical-map-cone f g c)
                ( vertical-map-cone (horizontal-map-cone f g c) h d)
                ( vertical-map-cone f g c x))
              ( inv-map-compute-fiber-comp g h (f (vertical-map-cone f g c x)))
              ( map-Σ
                ( λ t → fiber h (pr1 t))
                ( map-fiber-cone f g c (vertical-map-cone f g c x))
                ( λ t → map-fiber-cone (horizontal-map-cone f g c) h d (pr1 t)))
              ( map-fiber-cone f
                ( g ∘ h)
                ( pasting-vertical-cone f g h c d)
                ( vertical-map-cone f g c x))
              ( preserves-pasting-vertical-map-fiber-cone f g h c d
                ( vertical-map-cone f g c x))
              ( is-equiv-inv-map-compute-fiber-comp
                ( vertical-map-cone f g c)
                ( vertical-map-cone (horizontal-map-cone f g c) h d)
                ( vertical-map-cone f g c x))
              ( is-equiv-inv-map-compute-fiber-comp g h
                ( f (vertical-map-cone f g c x)))
              ( is-fiberwise-equiv-map-fiber-cone-is-pullback f
                ( g ∘ h)
                ( pasting-vertical-cone f g h c d)
                ( is-pb-dc)
                ( vertical-map-cone f g c x)))
            ( x , refl))

  abstract
    is-pullback-rectangle-is-pullback-top :
      (c : cone f g B) (d : cone (horizontal-map-cone f g c) h A) →
      is-pullback f g c →
      is-pullback (horizontal-map-cone f g c) h d →
      is-pullback f (g ∘ h) (pasting-vertical-cone f g h c d)
    is-pullback-rectangle-is-pullback-top c d is-pb-c is-pb-d =
      is-pullback-is-fiberwise-equiv-map-fiber-cone f (g ∘ h)
        ( pasting-vertical-cone f g h c d)
        ( λ x →
          is-equiv-bottom-is-equiv-top-square
            ( inv-map-compute-fiber-comp
              ( vertical-map-cone f g c)
              ( vertical-map-cone (horizontal-map-cone f g c) h d)
              ( x))
            ( inv-map-compute-fiber-comp g h (f x))
            ( map-Σ
              ( λ t → fiber h (pr1 t))
              ( map-fiber-cone f g c x)
              ( λ t → map-fiber-cone (horizontal-map-cone f g c) h d (pr1 t)))
            ( map-fiber-cone f (g ∘ h) (pasting-vertical-cone f g h c d) x)
            ( preserves-pasting-vertical-map-fiber-cone f g h c d x)
            ( is-equiv-inv-map-compute-fiber-comp
              ( vertical-map-cone f g c)
              ( vertical-map-cone (horizontal-map-cone f g c) h d)
              ( x))
            ( is-equiv-inv-map-compute-fiber-comp g h (f x))
            ( is-equiv-map-Σ
              ( λ t → fiber h (pr1 t))
              ( is-fiberwise-equiv-map-fiber-cone-is-pullback f g c is-pb-c x)
              ( λ t →
                is-fiberwise-equiv-map-fiber-cone-is-pullback
                  ( horizontal-map-cone f g c)
                  ( h)
                  ( d)
                  ( is-pb-d)
                  ( pr1 t))))
```

## Table of files about pullbacks

The following table lists files that are about pullbacks as a general concept.

{{#include tables/pullbacks.md}}
