# Pullbacks

```agda
module foundation.pullbacks where

open import foundation-core.pullbacks public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-cubes-of-maps
open import foundation.cones-over-cospans
open import foundation.dependent-pair-types
open import foundation.descent-equivalences
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.constant-maps
open import foundation-core.contractible-types
open import foundation-core.diagonal-maps-of-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-function-types
open import foundation-core.propositions
open import foundation-core.transport-along-identifications
open import foundation-core.whiskering-homotopies
```

</details>

## Properties

### Being a pullback is a property

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X)
  where

  is-property-is-pullback : (c : cone f g C) → is-prop (is-pullback f g c)
  is-property-is-pullback c = is-property-is-equiv (gap f g c)

  is-pullback-Prop : (c : cone f g C) → Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-pullback-Prop c = pair (is-pullback f g c) (is-property-is-pullback c)
```

### Exponents of pullbacks are pullbacks

```agda
exponent-cone :
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} (T : UU l5)
  (f : A → X) (g : B → X) (c : cone f g C) →
  cone (λ (h : T → A) → f ∘ h) (λ (h : T → B) → g ∘ h) (T → C)
pr1 (exponent-cone T f g c) h = vertical-map-cone f g c ∘ h
pr1 (pr2 (exponent-cone T f g c)) h = horizontal-map-cone f g c ∘ h
pr2 (pr2 (exponent-cone T f g c)) h = eq-htpy (coherence-square-cone f g c ·r h)

map-canonical-pullback-exponent :
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
  (T : UU l4) →
  canonical-pullback (λ (h : T → A) → f ∘ h) (λ (h : T → B) → g ∘ h) →
  cone f g T
map-canonical-pullback-exponent f g T =
  tot (λ p → tot (λ q → htpy-eq))

abstract
  is-equiv-map-canonical-pullback-exponent :
    {l1 l2 l3 l4 : Level}
    {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
    (T : UU l4) → is-equiv (map-canonical-pullback-exponent f g T)
  is-equiv-map-canonical-pullback-exponent f g T =
    is-equiv-tot-is-fiberwise-equiv
      ( λ p → is-equiv-tot-is-fiberwise-equiv
        ( λ q → funext (f ∘ p) (g ∘ q)))

triangle-map-canonical-pullback-exponent :
  {l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (T : UU l5) (f : A → X) (g : B → X) (c : cone f g C) →
  ( cone-map f g {C' = T} c) ~
  ( ( map-canonical-pullback-exponent f g T) ∘
    ( gap
      ( λ (h : T → A) → f ∘ h)
      ( λ (h : T → B) → g ∘ h)
      ( exponent-cone T f g c)))
triangle-map-canonical-pullback-exponent
  {A = A} {B} T f g c h =
  eq-pair-Σ refl
    ( eq-pair-Σ refl
      ( inv (is-section-eq-htpy (coherence-square-cone f g c ·r h))))

abstract
  is-pullback-exponent-is-pullback :
    {l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) (g : B → X) (c : cone f g C) → is-pullback f g c →
    (T : UU l5) →
    is-pullback
      ( λ (h : T → A) → f ∘ h)
      ( λ (h : T → B) → g ∘ h)
      ( exponent-cone T f g c)
  is-pullback-exponent-is-pullback f g c is-pb-c T =
    is-equiv-right-factor-htpy
      ( cone-map f g c)
      ( map-canonical-pullback-exponent f g T)
      ( gap (f ∘_) (g ∘_) (exponent-cone T f g c))
      ( triangle-map-canonical-pullback-exponent T f g c)
      ( is-equiv-map-canonical-pullback-exponent f g T)
      ( universal-property-pullback-is-pullback f g c is-pb-c T)

abstract
  is-pullback-is-pullback-exponent :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) (g : B → X) (c : cone f g C) →
    ((l5 : Level) (T : UU l5) → is-pullback
      ( λ (h : T → A) → f ∘ h)
      ( λ (h : T → B) → g ∘ h)
      ( exponent-cone T f g c)) →
    is-pullback f g c
  is-pullback-is-pullback-exponent f g c is-pb-exp =
    is-pullback-universal-property-pullback f g c
      ( λ T → is-equiv-comp-htpy
        ( cone-map f g c)
        ( map-canonical-pullback-exponent f g T)
        ( gap (_∘_ f) (_∘_ g) (exponent-cone T f g c))
        ( triangle-map-canonical-pullback-exponent T f g c)
        ( is-pb-exp _ T)
        ( is-equiv-map-canonical-pullback-exponent f g T))
```

### Identity types can be presented as pullbacks

```agda
cone-Id :
  {l : Level} {A : UU l} (x y : A) →
  cone (const unit A x) (const unit A y) (x ＝ y)
cone-Id x y =
  triple (const (x ＝ y) unit star) (const (x ＝ y) unit star) id

inv-gap-cone-Id :
  {l : Level} {A : UU l} (x y : A) →
  canonical-pullback (const unit A x) (const unit A y) → x ＝ y
inv-gap-cone-Id x y (pair star (pair star p)) = p

abstract
  is-section-inv-gap-cone-Id :
    {l : Level} {A : UU l} (x y : A) →
    ( ( gap (const unit A x) (const unit A y) (cone-Id x y)) ∘
      ( inv-gap-cone-Id x y)) ~ id
  is-section-inv-gap-cone-Id x y (pair star (pair star p)) = refl

abstract
  is-retraction-inv-gap-cone-Id :
    {l : Level} {A : UU l} (x y : A) →
    ( ( inv-gap-cone-Id x y) ∘
      ( gap (const unit A x) (const unit A y) (cone-Id x y))) ~ id
  is-retraction-inv-gap-cone-Id x y p = refl

abstract
  is-pullback-cone-Id :
    {l : Level} {A : UU l} (x y : A) →
    is-pullback (const unit A x) (const unit A y) (cone-Id x y)
  is-pullback-cone-Id x y =
    is-equiv-is-invertible
      ( inv-gap-cone-Id x y)
      ( is-section-inv-gap-cone-Id x y)
      ( is-retraction-inv-gap-cone-Id x y)

cone-Id' :
  {l : Level} {A : UU l} (t : A × A) →
  cone (const unit (A × A) t) (diagonal A) (pr1 t ＝ pr2 t)
cone-Id' {A = A} (pair x y) =
  triple
    ( const (x ＝ y) unit star)
    ( const (x ＝ y) A x)
    ( λ p → eq-pair-Σ refl (inv p))

inv-gap-cone-Id' :
  {l : Level} {A : UU l} (t : A × A) →
  canonical-pullback (const unit (A × A) t) (diagonal A) → (pr1 t ＝ pr2 t)
inv-gap-cone-Id' t (pair star (pair z p)) =
  (ap pr1 p) ∙ (inv (ap pr2 p))

abstract
  is-section-inv-gap-cone-Id' :
    {l : Level} {A : UU l} (t : A × A) →
    ( ( gap (const unit (A × A) t) (diagonal A) (cone-Id' t)) ∘
      ( inv-gap-cone-Id' t)) ~ id
  is-section-inv-gap-cone-Id' .(pair z z) (pair star (pair z refl)) = refl

abstract
  is-retraction-inv-gap-cone-Id' :
    {l : Level} {A : UU l} (t : A × A) →
    ( ( inv-gap-cone-Id' t) ∘
      ( gap (const unit (A × A) t) (diagonal A) (cone-Id' t))) ~ id
  is-retraction-inv-gap-cone-Id' (pair x .x) refl = refl

abstract
  is-pullback-cone-Id' :
    {l : Level} {A : UU l} (t : A × A) →
    is-pullback (const unit (A × A) t) (diagonal A) (cone-Id' t)
  is-pullback-cone-Id' t =
    is-equiv-is-invertible
      ( inv-gap-cone-Id' t)
      ( is-section-inv-gap-cone-Id' t)
      ( is-retraction-inv-gap-cone-Id' t)
```

### The equivalence on canonical pullbacks induced by parallel cospans

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  {f f' : A → X} (Hf : f ~ f') {g g' : B → X} (Hg : g ~ g')
  where

  map-equiv-canonical-pullback-htpy :
    canonical-pullback f' g' → canonical-pullback f g
  map-equiv-canonical-pullback-htpy =
    tot (λ a → tot (λ b →
      ( concat' (f a) (inv (Hg b))) ∘ (concat (Hf a) (g' b))))

  abstract
    is-equiv-map-equiv-canonical-pullback-htpy :
      is-equiv map-equiv-canonical-pullback-htpy
    is-equiv-map-equiv-canonical-pullback-htpy =
      is-equiv-tot-is-fiberwise-equiv (λ a →
        is-equiv-tot-is-fiberwise-equiv (λ b →
          is-equiv-comp
            ( concat' (f a) (inv (Hg b)))
            ( concat (Hf a) (g' b))
            ( is-equiv-concat (Hf a) (g' b))
            ( is-equiv-concat' (f a) (inv (Hg b)))))

  equiv-canonical-pullback-htpy :
    canonical-pullback f' g' ≃ canonical-pullback f g
  pr1 equiv-canonical-pullback-htpy = map-equiv-canonical-pullback-htpy
  pr2 equiv-canonical-pullback-htpy = is-equiv-map-equiv-canonical-pullback-htpy
```

### Parallel pullback squares

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  {f f' : A → X} (Hf : f ~ f') {g g' : B → X} (Hg : g ~ g')
  where

  triangle-is-pullback-htpy :
    {l4 : Level} {C : UU l4}
    {c : cone f g C} {c' : cone f' g' C} (Hc : htpy-parallel-cone Hf Hg c c') →
    (gap f g c) ~ (map-equiv-canonical-pullback-htpy Hf Hg ∘ (gap f' g' c'))
  triangle-is-pullback-htpy
    {c = pair p (pair q H)} {pair p' (pair q' H')} (pair Hp (pair Hq HH)) z =
    map-extensionality-canonical-pullback f g
      ( Hp z)
      ( Hq z)
      ( ( inv
          ( assoc
            ( ap f (Hp z))
            ( (Hf (p' z)) ∙ (H' z))
            ( inv (Hg (q' z))))) ∙
        ( inv
          ( right-transpose-eq-concat
            ( (H z) ∙ (ap g (Hq z)))
            ( Hg (q' z))
            ( ( ap f (Hp z)) ∙ ((Hf (p' z)) ∙ (H' z)))
            ( ( assoc (H z) (ap g (Hq z)) (Hg (q' z))) ∙
              ( ( HH z) ∙
                ( assoc (ap f (Hp z)) (Hf (p' z)) (H' z)))))))

  abstract
    is-pullback-htpy :
      {l4 : Level} {C : UU l4} {c : cone f g C} (c' : cone f' g' C)
      (Hc : htpy-parallel-cone Hf Hg c c') →
      is-pullback f' g' c' → is-pullback f g c
    is-pullback-htpy
      {c = pair p (pair q H)} (pair p' (pair q' H'))
      (pair Hp (pair Hq HH)) is-pb-c' =
      is-equiv-comp-htpy
        ( gap f g (triple p q H))
        ( map-equiv-canonical-pullback-htpy Hf Hg)
        ( gap f' g' (triple p' q' H'))
        ( triangle-is-pullback-htpy
          {c = triple p q H} {triple p' q' H'} (triple Hp Hq HH))
        ( is-pb-c')
        ( is-equiv-map-equiv-canonical-pullback-htpy Hf Hg)

  abstract
    is-pullback-htpy' :
      {l4 : Level} {C : UU l4} (c : cone f g C) {c' : cone f' g' C}
      (Hc : htpy-parallel-cone Hf Hg c c') →
      is-pullback f g c → is-pullback f' g' c'
    is-pullback-htpy'
      (pair p (pair q H)) {pair p' (pair q' H')}
      (pair Hp (pair Hq HH)) is-pb-c =
      is-equiv-right-factor-htpy
        ( gap f g (triple p q H))
        ( map-equiv-canonical-pullback-htpy Hf Hg)
        ( gap f' g' (triple p' q' H'))
        ( triangle-is-pullback-htpy
          {c = triple p q H} {triple p' q' H'} (triple Hp Hq HH))
        ( is-equiv-map-equiv-canonical-pullback-htpy Hf Hg)
        ( is-pb-c)
```

In the following part we will relate the type htpy-parallel-cone to the identity
type of cones. Here we will rely on function extensionality.

```agda
refl-htpy-parallel-cone :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c : cone f g C) →
  htpy-parallel-cone (refl-htpy {f = f}) (refl-htpy {f = g}) c c
refl-htpy-parallel-cone f g c =
  triple refl-htpy refl-htpy right-unit-htpy

htpy-eq-square :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c c' : cone f g C) →
  c ＝ c' → htpy-parallel-cone (refl-htpy {f = f}) (refl-htpy {f = g}) c c'
htpy-eq-square f g c .c refl =
  triple refl-htpy refl-htpy right-unit-htpy

htpy-parallel-cone-refl-htpy-htpy-cone :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) →
  (c c' : cone f g C) →
  htpy-cone f g c c' →
  htpy-parallel-cone (refl-htpy {f = f}) (refl-htpy {f = g}) c c'
htpy-parallel-cone-refl-htpy-htpy-cone f g
  (pair p (pair q H)) (pair p' (pair q' H')) =
  tot
    ( λ K → tot
      ( λ L M → ( ap-concat-htpy H _ _ right-unit-htpy) ∙h
        ( M ∙h ap-concat-htpy' _ _ H' inv-htpy-right-unit-htpy)))

abstract
  is-equiv-htpy-parallel-cone-refl-htpy-htpy-cone :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) (g : B → X) →
    (c c' : cone f g C) →
    is-equiv (htpy-parallel-cone-refl-htpy-htpy-cone f g c c')
  is-equiv-htpy-parallel-cone-refl-htpy-htpy-cone f g
    (pair p (pair q H)) (pair p' (pair q' H')) =
    is-equiv-tot-is-fiberwise-equiv
      ( λ K → is-equiv-tot-is-fiberwise-equiv
        ( λ L → is-equiv-comp
          ( concat-htpy
            ( ap-concat-htpy H _ _ right-unit-htpy)
            ( ((f ·l K) ∙h refl-htpy) ∙h H'))
          ( concat-htpy'
            ( H ∙h (g ·l L))
            ( ap-concat-htpy' _ _ H' inv-htpy-right-unit-htpy))
          ( is-equiv-concat-htpy'
            ( H ∙h (g ·l L))
            ( λ x → ap (λ z → z ∙ H' x) (inv right-unit)))
          ( is-equiv-concat-htpy
            ( λ x → ap (_∙_ (H x)) right-unit)
            ( ((f ·l K) ∙h refl-htpy) ∙h H'))))

abstract
  is-contr-total-htpy-parallel-cone-refl-htpy-refl-htpy :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) (g : B → X) →
    (c : cone f g C) →
    is-contr
      ( Σ (cone f g C) (htpy-parallel-cone (refl-htpy' f) (refl-htpy' g) c))
  is-contr-total-htpy-parallel-cone-refl-htpy-refl-htpy {A = A} {B} {X} {C}
    f g (pair p (pair q H)) =
    let c = triple p q H in
    is-contr-is-equiv'
      ( Σ (cone f g C) (htpy-cone f g c))
      ( tot (htpy-parallel-cone-refl-htpy-htpy-cone f g c))
      ( is-equiv-tot-is-fiberwise-equiv
        ( is-equiv-htpy-parallel-cone-refl-htpy-htpy-cone f g c))
      ( is-contr-total-htpy-cone f g c)

abstract
  is-contr-total-htpy-parallel-cone-refl-htpy :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) {g g' : B → X} (Hg : g ~ g') →
    (c : cone f g C) →
    is-contr (Σ (cone f g' C) (htpy-parallel-cone (refl-htpy' f) Hg c))
  is-contr-total-htpy-parallel-cone-refl-htpy {C = C} f {g} =
    ind-htpy g
      ( λ g'' Hg' → ( c : cone f g C) →
        is-contr (Σ (cone f g'' C) (htpy-parallel-cone (refl-htpy' f) Hg' c)))
      ( is-contr-total-htpy-parallel-cone-refl-htpy-refl-htpy f g)

abstract
  is-contr-total-htpy-parallel-cone :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    {f f' : A → X} (Hf : f ~ f') {g g' : B → X} (Hg : g ~ g') →
    (c : cone f g C) →
    is-contr (Σ (cone f' g' C) (htpy-parallel-cone Hf Hg c))
  is-contr-total-htpy-parallel-cone
    {A = A} {B} {X} {C} {f} {f'} Hf {g} {g'} Hg =
    ind-htpy
      { A = A}
      { B = λ t → X}
      ( f)
      ( λ f'' Hf' → (g g' : B → X) (Hg : g ~ g') (c : cone f g C) →
        is-contr (Σ (cone f'' g' C) (htpy-parallel-cone Hf' Hg c)))
      ( λ g g' Hg → is-contr-total-htpy-parallel-cone-refl-htpy f Hg)
      Hf g g' Hg

tr-tr-refl-htpy-cone :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c : cone f g C) →
  let tr-c = tr (λ x → cone x g C) (eq-htpy (refl-htpy {f = f})) c
      tr-tr-c = tr (λ y → cone f y C) (eq-htpy (refl-htpy {f = g})) tr-c
  in
  tr-tr-c ＝ c
tr-tr-refl-htpy-cone {C = C} f g c =
  let tr-c = tr (λ f''' → cone f''' g C) (eq-htpy refl-htpy) c
      tr-tr-c = tr (λ g'' → cone f g'' C) (eq-htpy refl-htpy) tr-c
      α : tr-tr-c ＝ tr-c
      α = ap (λ t → tr (λ g'' → cone f g'' C) t tr-c) (eq-htpy-refl-htpy g)
      β : tr-c ＝ c
      β = ap (λ t → tr (λ f''' → cone f''' g C) t c) (eq-htpy-refl-htpy f)
  in
  α ∙ β

htpy-eq-square-refl-htpy :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c c' : cone f g C) →
  let tr-c = tr (λ x → cone x g C) (eq-htpy (refl-htpy {f = f})) c
      tr-tr-c = tr (λ y → cone f y C) (eq-htpy (refl-htpy {f = g})) tr-c
  in
  tr-tr-c ＝ c' → htpy-parallel-cone (refl-htpy' f) (refl-htpy' g) c c'
htpy-eq-square-refl-htpy f g c c' =
  map-inv-is-equiv-precomp-Π-is-equiv
    ( is-equiv-concat (tr-tr-refl-htpy-cone f g c) c')
    ( λ p → htpy-parallel-cone (refl-htpy' f) (refl-htpy' g) c c')
    ( htpy-eq-square f g c c')

comp-htpy-eq-square-refl-htpy :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c c' : cone f g C) →
  ( (htpy-eq-square-refl-htpy f g c c') ∘
    (concat (tr-tr-refl-htpy-cone f g c) c')) ~
  ( htpy-eq-square f g c c')
comp-htpy-eq-square-refl-htpy f g c c' =
  is-section-map-inv-is-equiv-precomp-Π-is-equiv
    ( is-equiv-concat (tr-tr-refl-htpy-cone f g c) c')
    ( λ p → htpy-parallel-cone (refl-htpy' f) (refl-htpy' g) c c')
    ( htpy-eq-square f g c c')

abstract
  htpy-parallel-cone-eq' :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) {g g' : B → X} (Hg : g ~ g') →
    (c : cone f g C) (c' : cone f g' C) →
    let tr-c = tr (λ x → cone x g C) (eq-htpy (refl-htpy {f = f})) c
        tr-tr-c = tr (λ y → cone f y C) (eq-htpy Hg) tr-c
    in
    tr-tr-c ＝ c' → htpy-parallel-cone (refl-htpy' f) Hg c c'
  htpy-parallel-cone-eq' {C = C} f {g} =
    ind-htpy g
      ( λ g'' Hg' →
        ( c : cone f g C) (c' : cone f g'' C) →
        Id
          ( tr
            ( λ g'' → cone f g'' C)
            ( eq-htpy Hg')
            ( tr (λ f''' → cone f''' g C) (eq-htpy (refl-htpy' f)) c))
          ( c') →
        htpy-parallel-cone refl-htpy Hg' c c')
      ( htpy-eq-square-refl-htpy f g)

  comp-htpy-parallel-cone-eq' :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) (g : B → X) (c c' : cone f g C) →
    ( ( htpy-parallel-cone-eq' f refl-htpy c c') ∘
      ( concat (tr-tr-refl-htpy-cone f g c) c')) ~
    ( htpy-eq-square f g c c')
  comp-htpy-parallel-cone-eq' {A = A} {B} {X} {C} f g c c' =
    htpy-right-whisk
      ( htpy-eq (htpy-eq (htpy-eq (compute-ind-htpy g
        ( λ g'' Hg' →
          ( c : cone f g C) (c' : cone f g'' C) →
            Id (tr (λ g'' → cone f g'' C) (eq-htpy Hg')
              ( tr (λ f''' → cone f''' g C) (eq-htpy (refl-htpy' f)) c)) c' →
          htpy-parallel-cone refl-htpy Hg' c c')
      ( htpy-eq-square-refl-htpy f g)) c) c'))
      ( concat (tr-tr-refl-htpy-cone f g c) c') ∙h
    ( comp-htpy-eq-square-refl-htpy f g c c')

abstract
  htpy-parallel-cone-eq :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    {f f' : A → X} (Hf : f ~ f') {g g' : B → X} (Hg : g ~ g') →
    (c : cone f g C) (c' : cone f' g' C) →
    let tr-c = tr (λ x → cone x g C) (eq-htpy Hf) c
        tr-tr-c = tr (λ y → cone f' y C) (eq-htpy Hg) tr-c
    in
    Id tr-tr-c c' → htpy-parallel-cone Hf Hg c c'
  htpy-parallel-cone-eq {A = A} {B} {X} {C} {f} {f'} Hf {g} {g'} Hg c c' p =
    ind-htpy f
    ( λ f'' Hf' →
      ( g g' : B → X) (Hg : g ~ g') (c : cone f g C) (c' : cone f'' g' C) →
      ( Id (tr (λ g'' → cone f'' g'' C) (eq-htpy Hg)
        ( tr (λ f''' → cone f''' g C) (eq-htpy Hf') c)) c') →
      htpy-parallel-cone Hf' Hg c c')
    ( λ g g' → htpy-parallel-cone-eq' f {g = g} {g' = g'})
    Hf g g' Hg c c' p

  comp-htpy-parallel-cone-eq :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) (g : B → X) (c c' : cone f g C) →
    ( ( htpy-parallel-cone-eq refl-htpy refl-htpy c c') ∘
      ( concat (tr-tr-refl-htpy-cone f g c) c')) ~
    ( htpy-eq-square f g c c')
  comp-htpy-parallel-cone-eq {A = A} {B} {X} {C} f g c c' =
    htpy-right-whisk
      ( htpy-eq (htpy-eq (htpy-eq (htpy-eq (htpy-eq (htpy-eq (compute-ind-htpy f
        ( λ f'' Hf' →
          ( g g' : B → X) (Hg : g ~ g') (c : cone f g C) (c' : cone f'' g' C) →
            ( Id
              ( tr
                ( λ g'' → cone f'' g'' C)
                ( eq-htpy Hg)
                ( tr (λ f''' → cone f''' g C) (eq-htpy Hf') c)) c') →
            htpy-parallel-cone Hf' Hg c c')
        ( λ g g' → htpy-parallel-cone-eq' f {g = g} {g' = g'})) g) g)
        refl-htpy) c) c'))
      ( concat (tr-tr-refl-htpy-cone f g c) c') ∙h
      ( comp-htpy-parallel-cone-eq' f g c c')

abstract
  is-fiberwise-equiv-htpy-parallel-cone-eq :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    {f f' : A → X} (Hf : f ~ f') {g g' : B → X} (Hg : g ~ g') →
    (c : cone f g C) (c' : cone f' g' C) →
    is-equiv (htpy-parallel-cone-eq Hf Hg c c')
  is-fiberwise-equiv-htpy-parallel-cone-eq
    {A = A} {B} {X} {C} {f} {f'} Hf {g} {g'} Hg c c' =
    ind-htpy f
      ( λ f' Hf →
        ( g g' : B → X) (Hg : g ~ g') (c : cone f g C) (c' : cone f' g' C) →
          is-equiv (htpy-parallel-cone-eq Hf Hg c c'))
      ( λ g g' Hg c c' →
        ind-htpy g
          ( λ g' Hg →
            ( c : cone f g C) (c' : cone f g' C) →
              is-equiv (htpy-parallel-cone-eq refl-htpy Hg c c'))
          ( λ c c' →
            is-equiv-left-factor-htpy
              ( htpy-eq-square f g c c')
              ( htpy-parallel-cone-eq refl-htpy refl-htpy c c')
              ( concat (tr-tr-refl-htpy-cone f g c) c')
              ( inv-htpy (comp-htpy-parallel-cone-eq f g c c'))
              ( fundamental-theorem-id
                ( is-contr-total-htpy-parallel-cone
                  ( refl-htpy' f)
                  ( refl-htpy' g)
                  ( c))
                ( htpy-eq-square f g c) c')
              ( is-equiv-concat (tr-tr-refl-htpy-cone f g c) c'))
          Hg c c')
      Hf g g' Hg c c'

eq-htpy-parallel-cone :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  {f f' : A → X} (Hf : f ~ f') {g g' : B → X} (Hg : g ~ g') →
  (c : cone f g C) (c' : cone f' g' C) →
  let tr-c = tr (λ x → cone x g C) (eq-htpy Hf) c
      tr-tr-c = tr (λ y → cone f' y C) (eq-htpy Hg) tr-c
  in
  htpy-parallel-cone Hf Hg c c' → Id tr-tr-c c'
eq-htpy-parallel-cone Hf Hg c c' =
  map-inv-is-equiv
    { f = htpy-parallel-cone-eq Hf Hg c c'}
    ( is-fiberwise-equiv-htpy-parallel-cone-eq Hf Hg c c')
```

### Dependent products of pullbacks are pullbacks

```agda
cone-Π :
  {l1 l2 l3 l4 l5 : Level} {I : UU l1}
  {A : I → UU l2} {B : I → UU l3} {X : I → UU l4} {C : I → UU l5}
  (f : (i : I) → A i → X i) (g : (i : I) → B i → X i)
  (c : (i : I) → cone (f i) (g i) (C i)) →
  cone (map-Π f) (map-Π g) ((i : I) → C i)
cone-Π f g c =
  triple
    ( map-Π (λ i → pr1 (c i)))
    ( map-Π (λ i → pr1 (pr2 (c i))))
    ( htpy-map-Π (λ i → pr2 (pr2 (c i))))

map-canonical-pullback-Π :
  {l1 l2 l3 l4 : Level} {I : UU l1}
  {A : I → UU l2} {B : I → UU l3} {X : I → UU l4}
  (f : (i : I) → A i → X i) (g : (i : I) → B i → X i) →
  canonical-pullback (map-Π f) (map-Π g) →
  (i : I) → canonical-pullback (f i) (g i)
map-canonical-pullback-Π f g (pair α (pair β γ)) i =
  triple (α i) (β i) (htpy-eq γ i)

inv-map-canonical-pullback-Π :
  {l1 l2 l3 l4 : Level} {I : UU l1}
  {A : I → UU l2} {B : I → UU l3} {X : I → UU l4}
  (f : (i : I) → A i → X i) (g : (i : I) → B i → X i) →
  ((i : I) → canonical-pullback (f i) (g i)) →
  canonical-pullback (map-Π f) (map-Π g)
inv-map-canonical-pullback-Π f g h =
  triple
    ( λ i → (pr1 (h i)))
    ( λ i → (pr1 (pr2 (h i))))
    ( eq-htpy (λ i → (pr2 (pr2 (h i)))))

abstract
  is-section-inv-map-canonical-pullback-Π :
    {l1 l2 l3 l4 : Level} {I : UU l1}
    {A : I → UU l2} {B : I → UU l3} {X : I → UU l4}
    (f : (i : I) → A i → X i) (g : (i : I) → B i → X i) →
    ((map-canonical-pullback-Π f g) ∘ (inv-map-canonical-pullback-Π f g)) ~ id
  is-section-inv-map-canonical-pullback-Π f g h =
    eq-htpy
      ( λ i → map-extensionality-canonical-pullback (f i) (g i) refl refl
        ( inv
          ( ( right-unit) ∙
            ( htpy-eq (is-section-eq-htpy (λ i → (pr2 (pr2 (h i))))) i))))

abstract
  is-retraction-inv-map-canonical-pullback-Π :
    {l1 l2 l3 l4 : Level} {I : UU l1}
    {A : I → UU l2} {B : I → UU l3} {X : I → UU l4}
    (f : (i : I) → A i → X i) (g : (i : I) → B i → X i) →
    ((inv-map-canonical-pullback-Π f g) ∘ (map-canonical-pullback-Π f g)) ~ id
  is-retraction-inv-map-canonical-pullback-Π f g (pair α (pair β γ)) =
    map-extensionality-canonical-pullback
      ( map-Π f)
      ( map-Π g)
      refl
      refl
      ( inv (right-unit ∙ (is-retraction-eq-htpy γ)))

abstract
  is-equiv-map-canonical-pullback-Π :
    {l1 l2 l3 l4 : Level} {I : UU l1}
    {A : I → UU l2} {B : I → UU l3} {X : I → UU l4}
    (f : (i : I) → A i → X i) (g : (i : I) → B i → X i) →
    is-equiv (map-canonical-pullback-Π f g)
  is-equiv-map-canonical-pullback-Π f g =
    is-equiv-is-invertible
      ( inv-map-canonical-pullback-Π f g)
      ( is-section-inv-map-canonical-pullback-Π f g)
      ( is-retraction-inv-map-canonical-pullback-Π f g)

triangle-map-canonical-pullback-Π :
  {l1 l2 l3 l4 l5 : Level} {I : UU l1}
  {A : I → UU l2} {B : I → UU l3} {X : I → UU l4} {C : I → UU l5}
  (f : (i : I) → A i → X i) (g : (i : I) → B i → X i)
  (c : (i : I) → cone (f i) (g i) (C i)) →
  ( map-Π (λ i → gap (f i) (g i) (c i))) ~
  ( ( map-canonical-pullback-Π f g) ∘
    ( gap (map-Π f) (map-Π g) (cone-Π f g c)))
triangle-map-canonical-pullback-Π f g c h =
  eq-htpy (λ i →
    map-extensionality-canonical-pullback
      (f i)
      (g i)
      refl refl
      ( (htpy-eq (is-section-eq-htpy _) i) ∙ (inv right-unit)))

abstract
  is-pullback-cone-Π :
    {l1 l2 l3 l4 l5 : Level} {I : UU l1}
    {A : I → UU l2} {B : I → UU l3} {X : I → UU l4} {C : I → UU l5}
    (f : (i : I) → A i → X i) (g : (i : I) → B i → X i)
    (c : (i : I) → cone (f i) (g i) (C i)) →
    ((i : I) → is-pullback (f i) (g i) (c i)) →
    is-pullback (map-Π f) (map-Π g) (cone-Π f g c)
  is-pullback-cone-Π f g c is-pb-c =
    is-equiv-right-factor-htpy
      ( map-Π (λ i → gap (f i) (g i) (c i)))
      ( map-canonical-pullback-Π f g)
      ( gap (map-Π f) (map-Π g) (cone-Π f g c))
      ( triangle-map-canonical-pullback-Π f g c)
      ( is-equiv-map-canonical-pullback-Π f g)
      ( is-equiv-map-Π-is-fiberwise-equiv is-pb-c)
```

```agda
is-pullback-back-left-is-pullback-back-right-cube :
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  {f : A → B} {g : A → C} {h : B → D} {k : C → D}
  {A' : UU l1'} {B' : UU l2'} {C' : UU l3'} {D' : UU l4'}
  {f' : A' → B'} {g' : A' → C'} {h' : B' → D'} {k' : C' → D'}
  {hA : A' → A} {hB : B' → B} {hC : C' → C} {hD : D' → D}
  (top : (h' ∘ f') ~ (k' ∘ g'))
  (back-left : (f ∘ hA) ~ (hB ∘ f'))
  (back-right : (g ∘ hA) ~ (hC ∘ g'))
  (front-left : (h ∘ hB) ~ (hD ∘ h'))
  (front-right : (k ∘ hC) ~ (hD ∘ k'))
  (bottom : (h ∘ f) ~ (k ∘ g)) →
  (c : coherence-cube-maps f g h k f' g' h' k' hA hB hC hD
    top back-left back-right front-left front-right bottom) →
  is-pullback h hD (pair hB (pair h' front-left)) →
  is-pullback k hD (pair hC (pair k' front-right)) →
  is-pullback g hC (pair hA (pair g' back-right)) →
  is-pullback f hB (pair hA (pair f' back-left))
is-pullback-back-left-is-pullback-back-right-cube
  {f = f} {g} {h} {k} {f' = f'} {g'} {h'} {k'} {hA = hA} {hB} {hC} {hD}
  top back-left back-right front-left front-right bottom c
  is-pb-front-left is-pb-front-right is-pb-back-right =
  is-pullback-left-square-is-pullback-rectangle f h hD
    ( pair hB (pair h' front-left))
    ( pair hA (pair f' back-left))
    ( is-pb-front-left)
    ( is-pullback-htpy
      { f = h ∘ f}
      -- ( k ∘ g)
      ( bottom)
      { g = hD}
      -- ( hD)
      ( refl-htpy)
      { c = pair hA (pair (h' ∘ f')
        ( rectangle-left-cube
          f g h k f' g' h' k' hA hB hC hD
          top back-left back-right front-left front-right bottom))}
      ( pair hA (pair (k' ∘ g')
        ( rectangle-right-cube
          f g h k f' g' h' k' hA hB hC hD
          top back-left back-right front-left front-right bottom)))
      ( pair
        ( refl-htpy)
        ( pair top
          ( coherence-htpy-parallel-cone-rectangle-left-rectangle-right-cube
            f g h k f' g' h' k' hA hB hC hD
            top back-left back-right front-left front-right bottom c)))
      ( is-pullback-rectangle-is-pullback-left-square g k hD
        ( pair hC (pair k' front-right))
        ( pair hA (pair g' back-right))
        ( is-pb-front-right)
        ( is-pb-back-right)))

is-pullback-back-right-is-pullback-back-left-cube :
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  {f : A → B} {g : A → C} {h : B → D} {k : C → D}
  {A' : UU l1'} {B' : UU l2'} {C' : UU l3'} {D' : UU l4'}
  {f' : A' → B'} {g' : A' → C'} {h' : B' → D'} {k' : C' → D'}
  {hA : A' → A} {hB : B' → B} {hC : C' → C} {hD : D' → D}
  (top : (h' ∘ f') ~ (k' ∘ g'))
  (back-left : (f ∘ hA) ~ (hB ∘ f'))
  (back-right : (g ∘ hA) ~ (hC ∘ g'))
  (front-left : (h ∘ hB) ~ (hD ∘ h'))
  (front-right : (k ∘ hC) ~ (hD ∘ k'))
  (bottom : (h ∘ f) ~ (k ∘ g)) →
  (c : coherence-cube-maps f g h k f' g' h' k' hA hB hC hD
    top back-left back-right front-left front-right bottom) →
  is-pullback h hD (pair hB (pair h' front-left)) →
  is-pullback k hD (pair hC (pair k' front-right)) →
  is-pullback f hB (pair hA (pair f' back-left)) →
  is-pullback g hC (pair hA (pair g' back-right))
is-pullback-back-right-is-pullback-back-left-cube
  {f = f} {g} {h} {k} {f' = f'} {g'} {h'} {k'} {hA = hA} {hB} {hC} {hD}
  top back-left back-right front-left front-right bottom c
  is-pb-front-left is-pb-front-right is-pb-back-left =
  is-pullback-left-square-is-pullback-rectangle g k hD
    ( pair hC (pair k' front-right))
    ( pair hA (pair g' back-right))
    ( is-pb-front-right)
    ( is-pullback-htpy'
      { f' = k ∘ g}
      ( bottom)
      { g' = hD}
      ( refl-htpy)
      ( pair hA (pair (h' ∘ f')
        ( rectangle-left-cube
          f g h k f' g' h' k' hA hB hC hD
          top back-left back-right front-left front-right bottom)))
      { c' = pair hA (pair (k' ∘ g')
        ( rectangle-right-cube
          f g h k f' g' h' k' hA hB hC hD
          top back-left back-right front-left front-right bottom))}
      ( pair
        ( refl-htpy)
        ( pair top
          ( coherence-htpy-parallel-cone-rectangle-left-rectangle-right-cube
            f g h k f' g' h' k' hA hB hC hD
            top back-left back-right front-left front-right bottom c)))
      ( is-pullback-rectangle-is-pullback-left-square f h hD
        ( pair hB (pair h' front-left))
        ( pair hA (pair f' back-left))
        ( is-pb-front-left)
        ( is-pb-back-left)))
```

### In a commuting cube where the vertical maps are equivalences, the bottom square is a pullback if and only if the top square is a pullback

```agda
is-pullback-bottom-is-pullback-top-cube-is-equiv :
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : A → C) (h : B → D) (k : C → D)
  {A' : UU l1'} {B' : UU l2'} {C' : UU l3'} {D' : UU l4'}
  (f' : A' → B') (g' : A' → C') (h' : B' → D') (k' : C' → D')
  (hA : A' → A) (hB : B' → B) (hC : C' → C) (hD : D' → D)
  (top : (h' ∘ f') ~ (k' ∘ g'))
  (back-left : (f ∘ hA) ~ (hB ∘ f'))
  (back-right : (g ∘ hA) ~ (hC ∘ g'))
  (front-left : (h ∘ hB) ~ (hD ∘ h'))
  (front-right : (k ∘ hC) ~ (hD ∘ k'))
  (bottom : (h ∘ f) ~ (k ∘ g)) →
  (c :
    coherence-cube-maps f g h k f' g' h' k' hA hB hC hD
      top back-left back-right front-left front-right bottom) →
  is-equiv hA → is-equiv hB → is-equiv hC → is-equiv hD →
  is-pullback h' k' (pair f' (pair g' top)) →
  is-pullback h k (pair f (pair g bottom))
is-pullback-bottom-is-pullback-top-cube-is-equiv
  f g h k f' g' h' k' hA hB hC hD
  top back-left back-right front-left front-right bottom c
  is-equiv-hA is-equiv-hB is-equiv-hC is-equiv-hD is-pb-top =
  descent-is-equiv hB h k
    ( pair f (pair g bottom))
    ( pair f' (pair hA (inv-htpy (back-left))))
    ( is-equiv-hB)
    ( is-equiv-hA)
    ( is-pullback-htpy
      {f = h ∘ hB}
      -- ( hD ∘ h')
      ( front-left)
      {g = k}
      -- ( k)
      ( refl-htpy' k)
      { c = pair f'
        ( pair
          ( g ∘ hA)
          ( rectangle-back-left-bottom-cube
            f g h k f' g' h' k' hA hB hC hD
            top back-left back-right front-left front-right bottom))}
      ( pair
        ( f')
        ( pair
          ( hC ∘ g')
          ( rectangle-top-front-right-cube
            f g h k f' g' h' k' hA hB hC hD
            top back-left back-right front-left front-right bottom)))
      ( pair
        ( refl-htpy' f')
        ( pair
          ( back-right)
          ( coherence-htpy-parallel-cone-coherence-cube-maps
            f g h k f' g' h' k' hA hB hC hD
            top back-left back-right front-left front-right bottom c)))
      ( is-pullback-rectangle-is-pullback-left-square
        ( h')
        ( hD)
        ( k)
        ( pair k' (pair hC (inv-htpy front-right)))
        ( pair f' (pair g' top))
        ( is-pullback-is-equiv' hD k
          ( pair k' (pair hC (inv-htpy front-right)))
          ( is-equiv-hD)
          ( is-equiv-hC))
        ( is-pb-top)))

is-pullback-top-is-pullback-bottom-cube-is-equiv :
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : A → C) (h : B → D) (k : C → D)
  {A' : UU l1'} {B' : UU l2'} {C' : UU l3'} {D' : UU l4'}
  (f' : A' → B') (g' : A' → C') (h' : B' → D') (k' : C' → D')
  (hA : A' → A) (hB : B' → B) (hC : C' → C) (hD : D' → D)
  (top : (h' ∘ f') ~ (k' ∘ g'))
  (back-left : (f ∘ hA) ~ (hB ∘ f'))
  (back-right : (g ∘ hA) ~ (hC ∘ g'))
  (front-left : (h ∘ hB) ~ (hD ∘ h'))
  (front-right : (k ∘ hC) ~ (hD ∘ k'))
  (bottom : (h ∘ f) ~ (k ∘ g)) →
  (c :
    coherence-cube-maps f g h k f' g' h' k' hA hB hC hD
      top back-left back-right front-left front-right bottom) →
  is-equiv hA → is-equiv hB → is-equiv hC → is-equiv hD →
  is-pullback h k (pair f (pair g bottom)) →
  is-pullback h' k' (pair f' (pair g' top))
is-pullback-top-is-pullback-bottom-cube-is-equiv
  f g h k f' g' h' k' hA hB hC hD
  top back-left back-right front-left front-right bottom c
  is-equiv-hA is-equiv-hB is-equiv-hC is-equiv-hD is-pb-bottom =
  is-pullback-top-is-pullback-rectangle h hD k'
    ( pair hB (pair h' front-left))
    ( pair f' (pair g' top))
    ( is-pullback-is-equiv h hD
      ( pair hB (pair h' front-left))
      is-equiv-hD is-equiv-hB)
    ( is-pullback-htpy' refl-htpy front-right
      ( pasting-vertical-cone h k hC
        ( pair f (pair g bottom))
        ( pair hA (pair g' back-right)))
      { c' = pasting-vertical-cone h hD k'
        ( pair hB (pair h' front-left))
        ( pair f' (pair g' top))}
      ( pair back-left
        ( pair
          ( refl-htpy)
          ( ( ( ( assoc-htpy
                    ( bottom ·r hA) (k ·l back-right) (front-right ·r g')) ∙h
                ( inv-htpy c)) ∙h
              ( assoc-htpy
                  ( h ·l back-left) (front-left ·r f') (hD ·l top))) ∙h
            ( ap-concat-htpy'
              ( h ·l back-left)
              ( (h ·l back-left) ∙h refl-htpy)
              ( (front-left ·r f') ∙h (hD ·l top))
              ( inv-htpy-right-unit-htpy)))))
      ( is-pullback-rectangle-is-pullback-top h k hC
        ( pair f (pair g bottom))
        ( pair hA (pair g' back-right))
        ( is-pb-bottom)
        ( is-pullback-is-equiv g hC
          ( pair hA (pair g' back-right))
          is-equiv-hC is-equiv-hA)))
```

### In a commuting cube where the maps from back-right to front-left are equivalences, the back-right square is a pullback if and only if the front-left square is a pullback

```agda
is-pullback-front-left-is-pullback-back-right-cube-is-equiv :
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : A → C) (h : B → D) (k : C → D)
  {A' : UU l1'} {B' : UU l2'} {C' : UU l3'} {D' : UU l4'}
  (f' : A' → B') (g' : A' → C') (h' : B' → D') (k' : C' → D')
  (hA : A' → A) (hB : B' → B) (hC : C' → C) (hD : D' → D)
  (top : (h' ∘ f') ~ (k' ∘ g'))
  (back-left : (f ∘ hA) ~ (hB ∘ f'))
  (back-right : (g ∘ hA) ~ (hC ∘ g'))
  (front-left : (h ∘ hB) ~ (hD ∘ h'))
  (front-right : (k ∘ hC) ~ (hD ∘ k'))
  (bottom : (h ∘ f) ~ (k ∘ g)) →
  (c :
    coherence-cube-maps f g h k f' g' h' k' hA hB hC hD
      top back-left back-right front-left front-right bottom) →
  is-equiv f' → is-equiv f → is-equiv k' → is-equiv k →
  is-pullback g hC (pair hA (pair g' back-right)) →
  is-pullback h hD (pair hB (pair h' front-left))
is-pullback-front-left-is-pullback-back-right-cube-is-equiv
  f g h k f' g' h' k' hA hB hC hD
  top back-left back-right front-left front-right bottom c
  is-equiv-f' is-equiv-f is-equiv-k' is-equiv-k is-pb-back-right =
  is-pullback-bottom-is-pullback-top-cube-is-equiv
    hB h' h hD hA g' g hC f' f k' k
    back-right (inv-htpy back-left) top bottom (inv-htpy front-right) front-left
    ( coherence-cube-maps-mirror-B f g h k f' g' h' k' hA hB hC hD top
      back-left back-right front-left front-right bottom c)
    is-equiv-f' is-equiv-f is-equiv-k' is-equiv-k is-pb-back-right

is-pullback-front-right-is-pullback-back-left-cube-is-equiv :
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : A → C) (h : B → D) (k : C → D)
  {A' : UU l1'} {B' : UU l2'} {C' : UU l3'} {D' : UU l4'}
  (f' : A' → B') (g' : A' → C') (h' : B' → D') (k' : C' → D')
  (hA : A' → A) (hB : B' → B) (hC : C' → C) (hD : D' → D)
  (top : (h' ∘ f') ~ (k' ∘ g'))
  (back-left : (f ∘ hA) ~ (hB ∘ f'))
  (back-right : (g ∘ hA) ~ (hC ∘ g'))
  (front-left : (h ∘ hB) ~ (hD ∘ h'))
  (front-right : (k ∘ hC) ~ (hD ∘ k'))
  (bottom : (h ∘ f) ~ (k ∘ g)) →
  (c :
    coherence-cube-maps f g h k f' g' h' k' hA hB hC hD
      top back-left back-right front-left front-right bottom) →
  is-equiv g' → is-equiv h' → is-equiv g → is-equiv h →
  is-pullback f hB (pair hA (pair f' back-left)) →
  is-pullback k hD (pair hC (pair k' front-right))
is-pullback-front-right-is-pullback-back-left-cube-is-equiv
  f g h k f' g' h' k' hA hB hC hD
  top back-left back-right front-left front-right bottom c
  is-equiv-g' is-equiv-h' is-equiv-g is-equiv-h is-pb-back-left =
  is-pullback-bottom-is-pullback-top-cube-is-equiv
    hC k' k hD hA f' f hB g' g h' h
    back-left (inv-htpy back-right) (inv-htpy top)
    ( inv-htpy bottom) (inv-htpy front-left) front-right
    ( coherence-cube-maps-rotate-120 f g h k f' g' h' k' hA hB hC hD
      top back-left back-right front-left front-right bottom c)
    is-equiv-g' is-equiv-g is-equiv-h' is-equiv-h is-pb-back-left
```

### Identity types commute with pullbacks

```agda
cone-ap :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c : cone f g C) (c1 c2 : C) →
  let p = pr1 c
      q = pr1 (pr2 c)
      H = pr2 (pr2 c)
  in
  cone
    ( λ (α : Id (p c1) (p c2)) → (ap f α) ∙ (H c2))
    ( λ (β : Id (q c1) (q c2)) → (H c1) ∙ (ap g β))
    ( Id c1 c2)
pr1 (cone-ap f g (pair p (pair q H)) c1 c2) = ap p
pr1 (pr2 (cone-ap f g (pair p (pair q H)) c1 c2)) = ap q
pr2 (pr2 (cone-ap f g (pair p (pair q H)) c1 c2)) γ =
  ( ap (λ t → t ∙ (H c2)) (inv (ap-comp f p γ))) ∙
  ( ( inv-nat-htpy H γ) ∙
    ( ap (λ t → (H c1) ∙ t) (ap-comp g q γ)))

cone-ap' :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c : cone f g C) (c1 c2 : C) →
  let p = pr1 c
      q = pr1 (pr2 c)
      H = pr2 (pr2 c)
  in
  cone
    ( λ (α : Id (p c1) (p c2)) → tr (λ t → Id (f (p c1)) t) (H c2) (ap f α))
    ( λ (β : Id (q c1) (q c2)) → (H c1) ∙ (ap g β))
    ( Id c1 c2)
pr1 (cone-ap' f g (pair p (pair q H)) c1 c2) = ap p
pr1 (pr2 (cone-ap' f g (pair p (pair q H)) c1 c2)) = ap q
pr2 (pr2 (cone-ap' f g (pair p (pair q H)) c1 c2)) γ =
  ( tr-Id-right (H c2) (ap f (ap p γ))) ∙
  ( ( ap (λ t → t ∙ (H c2)) (inv (ap-comp f p γ))) ∙
    ( ( inv-nat-htpy H γ) ∙
      ( ap (λ t → (H c1) ∙ t) (ap-comp g q γ))))

is-pullback-cone-ap :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c : cone f g C) → is-pullback f g c →
  (c1 c2 : C) →
  let p = pr1 c
      q = pr1 (pr2 c)
      H = pr2 (pr2 c)
  in
  is-pullback
    ( λ (α : Id (vertical-map-cone f g c c1) (vertical-map-cone f g c c2)) →
      (ap f α) ∙ (coherence-square-cone f g c c2))
    ( λ (β : Id (horizontal-map-cone f g c c1) (horizontal-map-cone f g c c2)) →
      (H c1) ∙ (ap g β))
    ( cone-ap f g c c1 c2)
is-pullback-cone-ap f g (pair p (pair q H)) is-pb-c c1 c2 =
  is-pullback-htpy'
    ( λ α → tr-Id-right (H c2) (ap f α))
    ( refl-htpy)
    ( cone-ap' f g (pair p (pair q H)) c1 c2)
    { c' = cone-ap f g (pair p (pair q H)) c1 c2}
    ( pair refl-htpy (pair refl-htpy right-unit-htpy))
    ( is-pullback-family-is-pullback-tot
      ( λ x → Id (f (p c1)) x)
      ( λ a → ap f {x = p c1} {y = a})
      ( λ b β → (H c1) ∙ (ap g β))
      ( pair p (pair q H))
      ( cone-ap' f g (pair p (pair q H)) c1)
      ( is-pb-c)
      ( is-pullback-is-equiv
        ( map-Σ _ f (λ a α → ap f α))
        ( map-Σ _ g (λ b β → (H c1) ∙ (ap g β)))
        ( tot-cone-cone-family
          ( Id (f (p c1)))
          ( λ a → ap f)
          ( λ b β → (H c1) ∙ (ap g β))
          ( pair p (pair q H))
          ( cone-ap' f g (pair p (pair q H)) c1))
        ( is-equiv-is-contr _
          ( is-contr-total-path (q c1))
          ( is-contr-total-path (f (p c1))))
        ( is-equiv-is-contr _
          ( is-contr-total-path c1)
          ( is-contr-total-path (p c1))))
      ( c2))
```
