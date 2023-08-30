# Equivalences

```agda
module foundation.equivalences where

open import foundation-core.equivalences public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cones-over-cospans
open import foundation.dependent-pair-types
open import foundation.equivalence-extensionality
open import foundation.function-extensionality
open import foundation.functoriality-fibers-of-maps
open import foundation.identity-systems
open import foundation.identity-types
open import foundation.truncated-maps
open import foundation.type-theoretic-principle-of-choice
open import foundation.universe-levels

open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.embeddings
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.functoriality-function-types
open import foundation-core.homotopies
open import foundation-core.propositions
open import foundation-core.pullbacks
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.subtypes
open import foundation-core.truncation-levels
```

</details>

## Properties

### Any equivalence is an embedding

We already proved in `foundation-core.equivalences` that equivalences are
embeddings. Here we have `_↪_` available, so we record the map from equivalences
to embeddings.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  emb-equiv : (A ≃ B) → (A ↪ B)
  pr1 (emb-equiv e) = map-equiv e
  pr2 (emb-equiv e) = is-emb-is-equiv (is-equiv-map-equiv e)
```

### Transposing equalities along equivalences

The fact that equivalences are embeddings has many important consequences, we
will use some of these consequences in order to derive basic properties of
embeddings.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B)
  where

  eq-transpose-equiv :
    (x : A) (y : B) → (map-equiv e x ＝ y) ≃ (x ＝ map-inv-equiv e y)
  eq-transpose-equiv x y =
    ( inv-equiv (equiv-ap e x (map-inv-equiv e y))) ∘e
    ( equiv-concat'
      ( map-equiv e x)
      ( inv (is-section-map-inv-equiv e y)))

  map-eq-transpose-equiv :
    {x : A} {y : B} → map-equiv e x ＝ y → x ＝ map-inv-equiv e y
  map-eq-transpose-equiv {x} {y} = map-equiv (eq-transpose-equiv x y)

  inv-map-eq-transpose-equiv :
    {x : A} {y : B} → x ＝ map-inv-equiv e y → map-equiv e x ＝ y
  inv-map-eq-transpose-equiv {x} {y} = map-inv-equiv (eq-transpose-equiv x y)

  triangle-eq-transpose-equiv :
    {x : A} {y : B} (p : map-equiv e x ＝ y) →
    ( ( ap (map-equiv e) (map-eq-transpose-equiv p)) ∙
      ( is-section-map-inv-equiv e y)) ＝
    ( p)
  triangle-eq-transpose-equiv {x} {y} p =
    ( ap
      ( concat' (map-equiv e x) (is-section-map-inv-equiv e y))
      ( is-section-map-inv-equiv
        ( equiv-ap e x (map-inv-equiv e y))
        ( p ∙ inv (is-section-map-inv-equiv e y)))) ∙
    ( ( assoc
        ( p)
        ( inv (is-section-map-inv-equiv e y))
        ( is-section-map-inv-equiv e y)) ∙
      ( ( ap (concat p y) (left-inv (is-section-map-inv-equiv e y))) ∙
        ( right-unit)))

  map-eq-transpose-equiv' :
    {a : A} {b : B} → b ＝ map-equiv e a → map-inv-equiv e b ＝ a
  map-eq-transpose-equiv' p = inv (map-eq-transpose-equiv (inv p))

  inv-map-eq-transpose-equiv' :
    {a : A} {b : B} → map-inv-equiv e b ＝ a → b ＝ map-equiv e a
  inv-map-eq-transpose-equiv' p =
    inv (inv-map-eq-transpose-equiv (inv p))

  triangle-eq-transpose-equiv' :
    {x : A} {y : B} (p : y ＝ map-equiv e x) →
    ( (is-section-map-inv-equiv e y) ∙ p) ＝
    ( ap (map-equiv e) (map-eq-transpose-equiv' p))
  triangle-eq-transpose-equiv' {x} {y} p =
    map-inv-equiv
      ( equiv-ap
        ( equiv-inv (map-equiv e (map-inv-equiv e y)) (map-equiv e x))
        ( (is-section-map-inv-equiv e y) ∙ p)
        ( ap (map-equiv e) (map-eq-transpose-equiv' p)))
      ( ( distributive-inv-concat (is-section-map-inv-equiv e y) p) ∙
        ( ( inv
            ( con-inv
              ( ap (map-equiv e) (inv (map-eq-transpose-equiv' p)))
              ( is-section-map-inv-equiv e y)
              ( inv p)
              ( ( ap
                  ( concat' (map-equiv e x) (is-section-map-inv-equiv e y))
                  ( ap
                    ( ap (map-equiv e))
                    ( inv-inv
                      ( map-inv-equiv
                        ( equiv-ap e x (map-inv-equiv e y))
                        ( ( inv p) ∙
                          ( inv (is-section-map-inv-equiv e y))))))) ∙
                ( triangle-eq-transpose-equiv (inv p))))) ∙
          ( ap-inv (map-equiv e) (map-eq-transpose-equiv' p))))
```

### Equivalences have a contractible type of sections

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-contr-section-is-equiv : {f : A → B} → is-equiv f → is-contr (section f)
  is-contr-section-is-equiv {f} is-equiv-f =
    is-contr-equiv'
      ( (b : B) → fib f b)
      ( distributive-Π-Σ)
      ( is-contr-Π (is-contr-map-is-equiv is-equiv-f))
```

### Equivalences have a contractible type of retractions

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-contr-retraction-is-equiv :
    {f : A → B} → is-equiv f → is-contr (retraction f)
  is-contr-retraction-is-equiv {f} is-equiv-f =
    is-contr-is-equiv'
      ( Σ (B → A) (λ h → (h ∘ f) ＝ id))
      ( tot (λ h → htpy-eq))
      ( is-equiv-tot-is-fiberwise-equiv
        ( λ h → funext (h ∘ f) id))
      ( is-contr-map-is-equiv (is-equiv-precomp-is-equiv f is-equiv-f A) id)
```

### Being an equivalence is a property

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-contr-is-equiv-is-equiv : {f : A → B} → is-equiv f → is-contr (is-equiv f)
  is-contr-is-equiv-is-equiv is-equiv-f =
    is-contr-prod
      ( is-contr-section-is-equiv is-equiv-f)
      ( is-contr-retraction-is-equiv is-equiv-f)

  abstract
    is-property-is-equiv : (f : A → B) → (H K : is-equiv f) → is-contr (H ＝ K)
    is-property-is-equiv f H =
      is-prop-is-contr (is-contr-is-equiv-is-equiv H) H

  is-equiv-Prop : (f : A → B) → Prop (l1 ⊔ l2)
  pr1 (is-equiv-Prop f) = is-equiv f
  pr2 (is-equiv-Prop f) = is-property-is-equiv f

  eq-equiv-eq-map-equiv :
    {e e' : A ≃ B} → (map-equiv e) ＝ (map-equiv e') → e ＝ e'
  eq-equiv-eq-map-equiv = eq-type-subtype is-equiv-Prop

  abstract
    is-emb-map-equiv :
      is-emb (map-equiv {A = A} {B = B})
    is-emb-map-equiv = is-emb-inclusion-subtype is-equiv-Prop

  emb-map-equiv : (A ≃ B) ↪ (A → B)
  pr1 emb-map-equiv = map-equiv
  pr2 emb-map-equiv = is-emb-map-equiv
```

### The 3-for-2 property of being an equivalence

#### If the right factor is an equivalence, then the left factor being an equivalence is equivalent to the composite being one

```agda
module _
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  equiv-is-equiv-left-factor-htpy :
    { f : A → B} (e : B ≃ C) (h : A → C) (H : h ~ (map-equiv e ∘ f)) →
    is-equiv f ≃ is-equiv h
  equiv-is-equiv-left-factor-htpy {f} e h H =
    equiv-prop
      ( is-property-is-equiv f)
      ( is-property-is-equiv h)
      ( λ is-equiv-f →
        is-equiv-comp-htpy h (map-equiv e) f H is-equiv-f
          ( is-equiv-map-equiv e))
      ( is-equiv-right-factor-htpy h (map-equiv e) f H (is-equiv-map-equiv e))

  equiv-is-equiv-left-factor :
    { f : A → B} (e : B ≃ C) →
    is-equiv f ≃ is-equiv (map-equiv e ∘ f)
  equiv-is-equiv-left-factor {f} e =
    equiv-is-equiv-left-factor-htpy e (map-equiv e ∘ f) refl-htpy
```

#### If the left factor is an equivalence, then the right factor being an equivalence is equivalent to the composite being one

```agda
module _
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  equiv-is-equiv-right-factor-htpy :
    ( e : A ≃ B) {f : B → C} (h : A → C) (H : h ~ (f ∘ map-equiv e)) →
    is-equiv f ≃ is-equiv h
  equiv-is-equiv-right-factor-htpy e {f} h H =
    equiv-prop
      ( is-property-is-equiv f)
      ( is-property-is-equiv h)
      ( is-equiv-comp-htpy h f (map-equiv e) H (is-equiv-map-equiv e))
      ( λ is-equiv-h →
        is-equiv-left-factor-htpy h f (map-equiv e) H is-equiv-h
          ( is-equiv-map-equiv e))

  equiv-is-equiv-right-factor :
    ( e : A ≃ B) {f : B → C} →
    is-equiv f ≃ is-equiv (f ∘ map-equiv e)
  equiv-is-equiv-right-factor e {f} =
    equiv-is-equiv-right-factor-htpy e (f ∘ map-equiv e) refl-htpy
```

### Homotopy induction for homotopies between equivalences

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    Ind-htpy-equiv :
      {l3 : Level} (e : A ≃ B)
      (P : (e' : A ≃ B) (H : htpy-equiv e e') → UU l3) →
      section
        ( λ (h : (e' : A ≃ B) (H : htpy-equiv e e') → P e' H) →
          h e (refl-htpy-equiv e))
    Ind-htpy-equiv e =
      Ind-identity-system e
        ( refl-htpy-equiv e)
        ( is-contr-total-htpy-equiv e)

  ind-htpy-equiv :
    {l3 : Level} (e : A ≃ B) (P : (e' : A ≃ B) (H : htpy-equiv e e') → UU l3) →
    P e (refl-htpy-equiv e) → (e' : A ≃ B) (H : htpy-equiv e e') → P e' H
  ind-htpy-equiv e P = pr1 (Ind-htpy-equiv e P)

  compute-ind-htpy-equiv :
    {l3 : Level} (e : A ≃ B) (P : (e' : A ≃ B) (H : htpy-equiv e e') → UU l3)
    (p : P e (refl-htpy-equiv e)) →
    ind-htpy-equiv e P p e (refl-htpy-equiv e) ＝ p
  compute-ind-htpy-equiv e P = pr2 (Ind-htpy-equiv e P)
```

### The groupoid laws for equivalences

#### Equivalence composition is associative

```agda
associative-comp-equiv :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4} →
  (e : A ≃ B) (f : B ≃ C) (g : C ≃ D) →
  ((g ∘e f) ∘e e) ＝ (g ∘e (f ∘e e))
associative-comp-equiv e f g = eq-equiv-eq-map-equiv refl
```

#### Unit laws for equivalence composition

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where

  left-unit-law-equiv : (e : X ≃ Y) → (id-equiv ∘e e) ＝ e
  left-unit-law-equiv e = eq-equiv-eq-map-equiv refl

  right-unit-law-equiv : (e : X ≃ Y) → (e ∘e id-equiv) ＝ e
  right-unit-law-equiv e = eq-equiv-eq-map-equiv refl
```

#### Inverse laws for equivalence composition

```agda
  left-inverse-law-equiv : (e : X ≃ Y) → ((inv-equiv e) ∘e e) ＝ id-equiv
  left-inverse-law-equiv e =
    eq-htpy-equiv (is-retraction-map-inv-is-equiv (is-equiv-map-equiv e))

  right-inverse-law-equiv : (e : X ≃ Y) → (e ∘e (inv-equiv e)) ＝ id-equiv
  right-inverse-law-equiv e =
    eq-htpy-equiv (is-section-map-inv-is-equiv (is-equiv-map-equiv e))
```

#### `inv-equiv` is a fibered involution on equivalences

```agda
  inv-inv-equiv : (e : X ≃ Y) → (inv-equiv (inv-equiv e)) ＝ e
  inv-inv-equiv e = eq-equiv-eq-map-equiv refl

  inv-inv-equiv' : (e : Y ≃ X) → (inv-equiv (inv-equiv e)) ＝ e
  inv-inv-equiv' e = eq-equiv-eq-map-equiv refl

  is-equiv-inv-equiv : is-equiv (inv-equiv {A = X} {B = Y})
  is-equiv-inv-equiv =
    is-equiv-has-inverse
      ( inv-equiv)
      ( inv-inv-equiv')
      ( inv-inv-equiv)

  equiv-inv-equiv : (X ≃ Y) ≃ (Y ≃ X)
  pr1 equiv-inv-equiv = inv-equiv
  pr2 equiv-inv-equiv = is-equiv-inv-equiv
```

#### Higher coherence between the unit laws for equivalence composition

```agda
coh-unit-laws-equiv :
  {l : Level} {X : UU l} →
  left-unit-law-equiv (id-equiv {A = X}) ＝
  right-unit-law-equiv (id-equiv {A = X})
coh-unit-laws-equiv {l} {X} = ap eq-equiv-eq-map-equiv refl
```

#### Taking the inverse equivalence distributes over composition

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} {Z : UU l3}
  where

  distributive-inv-comp-equiv :
    (e : X ≃ Y) (f : Y ≃ Z) →
    (inv-equiv (f ∘e e)) ＝ ((inv-equiv e) ∘e (inv-equiv f))
  distributive-inv-comp-equiv e f =
    eq-htpy-equiv
      ( λ x →
        map-eq-transpose-equiv'
          ( f ∘e e)
          ( ( ap (λ g → map-equiv g x) (inv (right-inverse-law-equiv f))) ∙
            ( ap
              ( λ g → map-equiv (f ∘e (g ∘e (inv-equiv f))) x)
              ( inv (right-inverse-law-equiv e)))))
```

#### Iterated inverse laws for equivalence composition

```agda
left-left-inverse-law-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  (f : B ≃ C) (e : A ≃ B) → (inv-equiv f ∘e (f ∘e e)) ＝ e
left-left-inverse-law-equiv f e =
  eq-htpy-equiv (λ x → is-retraction-map-inv-equiv f (map-equiv e x))

left-right-inverse-law-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  (f : B ≃ C) (e : A ≃ C) →
  (f ∘e (inv-equiv f ∘e e)) ＝ e
left-right-inverse-law-equiv f e =
  eq-htpy-equiv (λ x → is-section-map-inv-equiv f (map-equiv e x))

right-right-inverse-law-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  (f : B ≃ C) (e : A ≃ B) →
  ((f ∘e e) ∘e inv-equiv e) ＝ f
right-right-inverse-law-equiv f e =
  eq-htpy-equiv (λ x → ap (map-equiv f) (is-section-map-inv-equiv e x))

right-left-inverse-law-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  (f : B ≃ C) (e : B ≃ A) →
  ((f ∘e inv-equiv e) ∘e e) ＝ f
right-left-inverse-law-equiv f e =
  eq-htpy-equiv (λ x → ap (map-equiv f) (is-retraction-map-inv-equiv e x))
```

### Left and right composition by an equivalence defines equivalences

```agda
is-equiv-left-comp-equiv :
  {l1 l2 l3 : Level} {B : UU l2} {C : UU l3}
  (f : B ≃ C) (A : UU l1) → is-equiv (λ (e : A ≃ B) → f ∘e e)
is-equiv-left-comp-equiv f A =
  is-equiv-has-inverse
    ( inv-equiv f ∘e_)
    ( left-right-inverse-law-equiv f)
    ( left-left-inverse-law-equiv f)

is-equiv-right-comp-equiv :
  {l1 l2 l3 : Level} {A : UU l2} {B : UU l3}
  (C : UU l1) (e : A ≃ B) → is-equiv (λ (f : B ≃ C) → f ∘e e)
is-equiv-right-comp-equiv A e =
  is-equiv-has-inverse
    ( _∘e inv-equiv e)
    ( λ f → right-left-inverse-law-equiv f e)
    ( λ f → right-right-inverse-law-equiv f e)

equiv-postcomp-equiv :
  {l1 l2 l3 : Level} {B : UU l2} {C : UU l3} →
  (f : B ≃ C) → (A : UU l1) → (A ≃ B) ≃ (A ≃ C)
pr1 (equiv-postcomp-equiv f A) e = f ∘e e
pr2 (equiv-postcomp-equiv f A) = is-equiv-left-comp-equiv f A
```

```agda
equiv-precomp-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} →
  (A ≃ B) → (C : UU l3) → (B ≃ C) ≃ (A ≃ C)
pr1 (equiv-precomp-equiv e C) f = f ∘e e
pr2 (equiv-precomp-equiv e C) = is-equiv-right-comp-equiv C e
```

### A cospan in which one of the legs is an equivalence is a pullback if and only if the corresponding map on the cone is an equivalence

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {X : UU l4} (f : A → X) (g : B → X) (c : cone f g C)
  where

  abstract
    is-equiv-is-pullback : is-equiv g → is-pullback f g c → is-equiv (pr1 c)
    is-equiv-is-pullback is-equiv-g pb =
      is-equiv-is-contr-map
        ( is-trunc-is-pullback neg-two-𝕋 f g c pb
          ( is-contr-map-is-equiv is-equiv-g))

  abstract
    is-pullback-is-equiv : is-equiv g → is-equiv (pr1 c) → is-pullback f g c
    is-pullback-is-equiv is-equiv-g is-equiv-p =
      is-pullback-is-fiberwise-equiv-map-fib-cone f g c
        ( λ a → is-equiv-is-contr
          ( map-fib-cone f g c a)
          ( is-contr-map-is-equiv is-equiv-p a)
          ( is-contr-map-is-equiv is-equiv-g (f a)))
```

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {X : UU l4} (f : A → X) (g : B → X) (c : cone f g C)
  where

  abstract
    is-equiv-is-pullback' :
      is-equiv f → is-pullback f g c → is-equiv (pr1 (pr2 c))
    is-equiv-is-pullback' is-equiv-f pb =
      is-equiv-is-contr-map
        ( is-trunc-is-pullback' neg-two-𝕋 f g c pb
          ( is-contr-map-is-equiv is-equiv-f))

  abstract
    is-pullback-is-equiv' :
      is-equiv f → is-equiv (pr1 (pr2 c)) → is-pullback f g c
    is-pullback-is-equiv' is-equiv-f is-equiv-q =
      is-pullback-swap-cone' f g c
        ( is-pullback-is-equiv g f
          ( swap-cone f g c)
          is-equiv-f
          is-equiv-q)
```

### Families of equivalences are equivalent to fiberwise equivalences

```agda
equiv-fiberwise-equiv-fam-equiv :
  {l1 l2 l3 : Level} {A : UU l1} (B : A → UU l2) (C : A → UU l3) →
  fam-equiv B C ≃ fiberwise-equiv B C
equiv-fiberwise-equiv-fam-equiv B C = distributive-Π-Σ
```

## See also

- For the notions of inverses and coherently invertible maps, also known as
  half-adjoint equivalences, see
  [`foundation.coherently-invertible-maps`](foundation.coherently-invertible-maps.md).
- For the notion of maps with contractible fibers see
  [`foundation.contractible-maps`](foundation.contractible-maps.md).
- For the notion of path-split maps see
  [`foundation.path-split-maps`](foundation.path-split-maps.md).
