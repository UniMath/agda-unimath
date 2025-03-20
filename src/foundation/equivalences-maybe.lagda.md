# Equivalences on `Maybe`

```agda
open import foundation.function-extensionality-axiom

module
  foundation.equivalences-maybe
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equality-coproduct-types funext
open import foundation.equivalence-extensionality funext
open import foundation.equivalences funext
open import foundation.functoriality-coproduct-types funext
open import foundation.maybe funext
open import foundation.unit-type
open import foundation.universal-property-maybe funext
open import foundation.universe-levels

open import foundation-core.coproduct-types
open import foundation-core.embeddings
open import foundation-core.empty-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.propositions
open import foundation-core.sets
```

</details>

## Idea

For any two types `X` and `Y`, we have `(X ≃ Y) ↔ (Maybe X ≃ Maybe Y)`.

## Definition

### The action of the maybe monad on equivalences

```agda
equiv-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : X ≃ Y) → Maybe X ≃ Maybe Y
equiv-Maybe e = equiv-coproduct e id-equiv
```

### Equivalences of maybe structures on a type

```agda
equiv-maybe-structure :
  {l1 : Level} {X : UU l1} (Y Z : maybe-structure X) → UU l1
equiv-maybe-structure Y Z =
  Σ (pr1 Y ≃ pr1 Z) (λ e → htpy-equiv (pr2 Y) (pr2 Z ∘e equiv-Maybe e))

id-equiv-maybe-structure :
  {l1 : Level} {X : UU l1} (Y : maybe-structure X) → equiv-maybe-structure Y Y
id-equiv-maybe-structure Y =
  pair id-equiv (ind-Maybe (pair refl-htpy refl))

equiv-eq-maybe-structure :
  {l1 : Level} {X : UU l1} (Y Z : maybe-structure X) →
  Y ＝ Z → equiv-maybe-structure Y Z
equiv-eq-maybe-structure Y .Y refl = id-equiv-maybe-structure Y
```

## Properties

### If `f : Maybe X → Maybe Y` is an injective map and `f (inl x)` is an exception, then `f exception` is not an exception

```agda
abstract
  is-not-exception-injective-map-exception-Maybe :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
    is-injective f → (x : X) → is-exception-Maybe (f (inl x)) →
    is-not-exception-Maybe (f exception-Maybe)
  is-not-exception-injective-map-exception-Maybe is-inj-f x p q =
    is-not-exception-unit-Maybe x (is-inj-f (p ∙ inv q))

abstract
  is-not-exception-map-equiv-exception-Maybe :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (x : X) →
    is-exception-Maybe (map-equiv e (inl x)) →
    is-not-exception-Maybe (map-equiv e exception-Maybe)
  is-not-exception-map-equiv-exception-Maybe e =
    is-not-exception-injective-map-exception-Maybe (is-injective-equiv e)

abstract
  is-not-exception-emb-exception-Maybe :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ↪ Maybe Y)
    (x : X) → is-exception-Maybe (map-emb e (inl x)) →
    is-not-exception-Maybe (map-emb e exception-Maybe)
  is-not-exception-emb-exception-Maybe e =
    is-not-exception-injective-map-exception-Maybe (is-injective-emb e)
```

### If `f` is injective and `f (inl x)` is an exception, then `f exception` is a value

```agda
is-value-injective-map-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  is-injective f → (x : X) → is-exception-Maybe (f (inl x)) →
  is-value-Maybe (f exception-Maybe)
is-value-injective-map-exception-Maybe {f = f} is-inj-f x H =
  is-value-is-not-exception-Maybe
    ( f exception-Maybe)
    ( is-not-exception-injective-map-exception-Maybe is-inj-f x H)

value-injective-map-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  is-injective f → (x : X) → is-exception-Maybe (f (inl x)) → Y
value-injective-map-exception-Maybe {f = f} is-inj-f x H =
  value-is-value-Maybe
    ( f exception-Maybe)
    ( is-value-injective-map-exception-Maybe is-inj-f x H)

comp-injective-map-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  (is-inj-f : is-injective f) (x : X) (H : is-exception-Maybe (f (inl x))) →
  inl (value-injective-map-exception-Maybe is-inj-f x H) ＝
  f exception-Maybe
comp-injective-map-exception-Maybe {f = f} is-inj-f x H =
  eq-is-value-Maybe
    ( f exception-Maybe)
    ( is-value-injective-map-exception-Maybe is-inj-f x H)
```

### For any equivalence `e : Maybe X ≃ Maybe Y`, if `e (inl x)` is an exception, then `e exception` is a value

```agda
is-value-map-equiv-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (x : X) →
  is-exception-Maybe (map-equiv e (inl x)) →
  is-value-Maybe (map-equiv e exception-Maybe)
is-value-map-equiv-exception-Maybe e x H =
  is-value-is-not-exception-Maybe
    ( map-equiv e exception-Maybe)
    ( is-not-exception-map-equiv-exception-Maybe e x H)

value-map-equiv-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (x : X) →
  is-exception-Maybe (map-equiv e (inl x)) → Y
value-map-equiv-exception-Maybe e x H =
  value-is-value-Maybe
    ( map-equiv e exception-Maybe)
    ( is-value-map-equiv-exception-Maybe e x H)

compute-map-equiv-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (x : X) →
  (H : is-exception-Maybe (map-equiv e (inl x))) →
  inl (value-map-equiv-exception-Maybe e x H) ＝ map-equiv e exception-Maybe
compute-map-equiv-exception-Maybe e x H =
  eq-is-value-Maybe
    ( map-equiv e exception-Maybe)
    ( is-value-map-equiv-exception-Maybe e x H)
```

### Injective maps `Maybe X → Maybe Y` can be restricted to maps `X → Y`

```agda
restrict-injective-map-Maybe' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  is-injective f → (x : X) (u : Maybe Y) (p : f (inl x) ＝ u) → Y
restrict-injective-map-Maybe' {f = f} is-inj-f x (inl y) p = y
restrict-injective-map-Maybe' {f = f} is-inj-f x (inr star) p =
  value-injective-map-exception-Maybe is-inj-f x p

restrict-injective-map-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  is-injective f → X → Y
restrict-injective-map-Maybe {f = f} is-inj-f x =
  restrict-injective-map-Maybe' is-inj-f x (f (inl x)) refl

compute-restrict-injective-map-is-exception-Maybe' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  (is-inj-f : is-injective f) (x : X) (u : Maybe Y) (p : f (inl x) ＝ u) →
  is-exception-Maybe (f (inl x)) →
  inl (restrict-injective-map-Maybe' is-inj-f x u p) ＝ f exception-Maybe
compute-restrict-injective-map-is-exception-Maybe'
  {f = f} is-inj-f x (inl y) p q =
  ex-falso (is-not-exception-unit-Maybe y (inv p ∙ q))
compute-restrict-injective-map-is-exception-Maybe'
  {f = f} is-inj-f x (inr star) p q =
  comp-injective-map-exception-Maybe is-inj-f x p

compute-restrict-injective-map-is-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  (is-inj-f : is-injective f) (x : X) → is-exception-Maybe (f (inl x)) →
  inl (restrict-injective-map-Maybe is-inj-f x) ＝ f exception-Maybe
compute-restrict-injective-map-is-exception-Maybe {f = f} is-inj-f x =
  compute-restrict-injective-map-is-exception-Maybe' is-inj-f x (f (inl x)) refl

compute-restrict-injective-map-is-not-exception-Maybe' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  (is-inj-f : is-injective f) (x : X) (u : Maybe Y) (p : f (inl x) ＝ u) →
  is-not-exception-Maybe (f (inl x)) →
  inl (restrict-injective-map-Maybe' is-inj-f x u p) ＝ f (inl x)
compute-restrict-injective-map-is-not-exception-Maybe'
  is-inj-f x (inl y) p H =
  inv p
compute-restrict-injective-map-is-not-exception-Maybe'
  is-inj-f x (inr star) p H =
  ex-falso (H p)

compute-restrict-injective-map-is-not-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : Maybe X → Maybe Y} →
  (is-inj-f : is-injective f) (x : X) → is-not-exception-Maybe (f (inl x)) →
  inl (restrict-injective-map-Maybe is-inj-f x) ＝ f (inl x)
compute-restrict-injective-map-is-not-exception-Maybe {f = f} is-inj-f x =
  compute-restrict-injective-map-is-not-exception-Maybe' is-inj-f x (f (inl x))
    refl
```

### Any equivalence `Maybe X ≃ Maybe Y` induces a map `X → Y`

We don't use with-abstraction to keep full control over the definitional
equalities, so we give the definition in two steps. After the definition is
complete, we also prove two computation rules. Since we will prove computation
rules, we make the definition abstract.

```agda
map-equiv-equiv-Maybe' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y)
  (x : X) (u : Maybe Y) (p : map-equiv e (inl x) ＝ u) → Y
map-equiv-equiv-Maybe' e =
  restrict-injective-map-Maybe' (is-injective-equiv e)

map-equiv-equiv-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) → X → Y
map-equiv-equiv-Maybe e =
  restrict-injective-map-Maybe (is-injective-equiv e)

compute-map-equiv-equiv-is-exception-Maybe' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (x : X) →
  (u : Maybe Y) (p : map-equiv e (inl x) ＝ u) →
  is-exception-Maybe (map-equiv e (inl x)) →
  inl (map-equiv-equiv-Maybe' e x u p) ＝ map-equiv e exception-Maybe
compute-map-equiv-equiv-is-exception-Maybe' e =
  compute-restrict-injective-map-is-exception-Maybe' (is-injective-equiv e)

compute-map-equiv-equiv-is-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (x : X) →
  is-exception-Maybe (map-equiv e (inl x)) →
  inl (map-equiv-equiv-Maybe e x) ＝ map-equiv e exception-Maybe
compute-map-equiv-equiv-is-exception-Maybe e x =
  compute-map-equiv-equiv-is-exception-Maybe' e x (map-equiv e (inl x)) refl

compute-map-equiv-equiv-is-not-exception-Maybe' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (x : X) →
  (u : Maybe Y) (p : map-equiv e (inl x) ＝ u) →
  is-not-exception-Maybe (map-equiv e (inl x)) →
  inl (map-equiv-equiv-Maybe' e x u p) ＝ map-equiv e (inl x)
compute-map-equiv-equiv-is-not-exception-Maybe' e x (inl y) p H =
  inv p
compute-map-equiv-equiv-is-not-exception-Maybe' e x (inr star) p H =
  ex-falso (H p)

compute-map-equiv-equiv-is-not-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (x : X) →
  is-not-exception-Maybe (map-equiv e (inl x)) →
  inl (map-equiv-equiv-Maybe e x) ＝ map-equiv e (inl x)
compute-map-equiv-equiv-is-not-exception-Maybe e x =
  compute-map-equiv-equiv-is-not-exception-Maybe' e x (map-equiv e (inl x)) refl
```

### Any equivalence `Maybe X ≃ Maybe Y` induces a map `Y → X`

```agda
map-inv-equiv-equiv-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) → Y → X
map-inv-equiv-equiv-Maybe e =
  map-equiv-equiv-Maybe (inv-equiv e)

compute-map-inv-equiv-equiv-is-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (y : Y) →
  is-exception-Maybe (map-inv-equiv e (inl y)) →
  inl (map-inv-equiv-equiv-Maybe e y) ＝ map-inv-equiv e exception-Maybe
compute-map-inv-equiv-equiv-is-exception-Maybe e =
  compute-map-equiv-equiv-is-exception-Maybe (inv-equiv e)

compute-map-inv-equiv-equiv-is-not-exception-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) (y : Y) →
  ( f : is-not-exception-Maybe (map-inv-equiv e (inl y))) →
  inl (map-inv-equiv-equiv-Maybe e y) ＝ map-inv-equiv e (inl y)
compute-map-inv-equiv-equiv-is-not-exception-Maybe e =
  compute-map-equiv-equiv-is-not-exception-Maybe (inv-equiv e)
```

### The map `map-inv-equiv-equiv-Maybe e` is a section of `map-equiv-equiv-Maybe e`

```agda
abstract
  is-section-map-inv-equiv-equiv-Maybe :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) →
    (map-equiv-equiv-Maybe e ∘ map-inv-equiv-equiv-Maybe e) ~ id
  is-section-map-inv-equiv-equiv-Maybe e y with
    is-decidable-is-exception-Maybe (map-inv-equiv e (inl y))
  ... | inl p =
    is-injective-unit-Maybe
      ( ( compute-map-equiv-equiv-is-exception-Maybe e
          ( map-inv-equiv-equiv-Maybe e y)
          ( ( ap
              ( map-equiv e)
              ( compute-map-inv-equiv-equiv-is-exception-Maybe e y p)) ∙
            ( is-section-map-inv-equiv e exception-Maybe))) ∙
        ( ( ap (map-equiv e) (inv p)) ∙
          ( is-section-map-inv-equiv e (inl y))))
  ... | inr f =
    is-injective-unit-Maybe
      ( ( compute-map-equiv-equiv-is-not-exception-Maybe e
          ( map-inv-equiv-equiv-Maybe e y)
          ( is-not-exception-is-value-Maybe
            ( map-equiv e (inl (map-inv-equiv-equiv-Maybe e y)))
            ( pair y
              ( inv
                ( ( ap
                    ( map-equiv e)
                    ( compute-map-inv-equiv-equiv-is-not-exception-Maybe
                        e y f)) ∙
                  ( is-section-map-inv-equiv e (inl y))))))) ∙
        ( ( ap
            ( map-equiv e)
            ( compute-map-inv-equiv-equiv-is-not-exception-Maybe e y f)) ∙
          ( is-section-map-inv-equiv e (inl y))))
```

### The map `map-inv-equiv-equiv-Maybe e` is a retraction of the map `map-equiv-equiv-Maybe e`

```agda
abstract
  is-retraction-map-inv-equiv-equiv-Maybe :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) →
    (map-inv-equiv-equiv-Maybe e ∘ map-equiv-equiv-Maybe e) ~ id
  is-retraction-map-inv-equiv-equiv-Maybe e x with
    is-decidable-is-exception-Maybe (map-equiv e (inl x))
  ... | inl p =
    is-injective-unit-Maybe
      ( ( compute-map-inv-equiv-equiv-is-exception-Maybe e
          ( map-equiv-equiv-Maybe e x)
          ( ( ap
              ( map-inv-equiv e)
              ( compute-map-equiv-equiv-is-exception-Maybe e x p)) ∙
            ( is-retraction-map-inv-equiv e exception-Maybe))) ∙
        ( ( ap (map-inv-equiv e) (inv p)) ∙
          ( is-retraction-map-inv-equiv e (inl x))))
  ... | inr f =
    is-injective-unit-Maybe
      ( ( compute-map-inv-equiv-equiv-is-not-exception-Maybe e
          ( map-equiv-equiv-Maybe e x)
          ( is-not-exception-is-value-Maybe
            ( map-inv-equiv e (inl (map-equiv-equiv-Maybe e x)))
            ( pair x
              ( inv
                ( ( ap
                    ( map-inv-equiv e)
                    ( compute-map-equiv-equiv-is-not-exception-Maybe
                        e x f)) ∙
                  ( is-retraction-map-inv-equiv e (inl x))))))) ∙
        ( ( ap
            ( map-inv-equiv e)
            ( compute-map-equiv-equiv-is-not-exception-Maybe e x f)) ∙
          ( is-retraction-map-inv-equiv e (inl x))))
```

### The function `map-equiv-equiv-Maybe` is an equivalence

```agda
abstract
  is-equiv-map-equiv-equiv-Maybe :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : Maybe X ≃ Maybe Y) →
    is-equiv (map-equiv-equiv-Maybe e)
  is-equiv-map-equiv-equiv-Maybe e =
    is-equiv-is-invertible
      ( map-inv-equiv-equiv-Maybe e)
      ( is-section-map-inv-equiv-equiv-Maybe e)
      ( is-retraction-map-inv-equiv-equiv-Maybe e)

equiv-equiv-Maybe :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → (Maybe X ≃ Maybe Y) → (X ≃ Y)
pr1 (equiv-equiv-Maybe e) = map-equiv-equiv-Maybe e
pr2 (equiv-equiv-Maybe e) = is-equiv-map-equiv-equiv-Maybe e

compute-equiv-equiv-Maybe-id-equiv :
  {l1 : Level} {X : UU l1} →
  equiv-equiv-Maybe id-equiv ＝ id-equiv {A = X}
compute-equiv-equiv-Maybe-id-equiv = eq-htpy-equiv refl-htpy
```

### For any set `X`, the type of automorphisms on `X` is equivalent to the type of automorphisms on `Maybe X` that fix the exception

```agda
module _
  {l : Level} (X : Set l)
  where

  extend-equiv-Maybe :
    (type-Set X ≃ type-Set X) ≃
    ( Σ ( Maybe (type-Set X) ≃ Maybe (type-Set X))
        ( λ e → map-equiv e (inr star) ＝ inr star))
  pr1 (pr1 extend-equiv-Maybe f) = equiv-coproduct f id-equiv
  pr2 (pr1 extend-equiv-Maybe f) = refl
  pr2 extend-equiv-Maybe =
    is-equiv-is-invertible
      ( λ f → pr1 (retraction-equiv-coproduct (pr1 f) id-equiv (p f)))
      ( λ f →
        ( eq-pair-Σ
          ( inv
            ( eq-htpy-equiv
              ( pr2 (retraction-equiv-coproduct (pr1 f) id-equiv (p f)))))
          ( eq-is-prop
            ( pr2
              ( Id-Prop
                ( pair
                  ( Maybe (type-Set X))
                  ( is-set-coproduct (is-set-type-Set X) is-set-unit))
                ( map-equiv (pr1 f) (inr star))
                ( inr star))))))
      ( λ f → eq-equiv-eq-map-equiv refl)
    where
    p :
      ( f :
        ( Σ ( Maybe (type-Set X) ≃ Maybe (type-Set X))
            ( λ e → map-equiv e (inr star) ＝ inr star)))
      ( b : unit) →
      map-equiv (pr1 f) (inr b) ＝ inr b
    p f star = pr2 f

  computation-extend-equiv-Maybe :
    (f : type-Set X ≃ type-Set X) (x y : type-Set X) → map-equiv f x ＝ y →
    map-equiv (pr1 (map-equiv extend-equiv-Maybe f)) (inl x) ＝ inl y
  computation-extend-equiv-Maybe f x y p = ap inl p

  computation-inv-extend-equiv-Maybe :
    (f : Maybe (type-Set X) ≃ Maybe (type-Set X))
    (p : map-equiv f (inr star) ＝ inr star) (x : type-Set X) →
    inl (map-equiv (map-inv-equiv extend-equiv-Maybe (pair f p)) x) ＝
    map-equiv f (inl x)
  computation-inv-extend-equiv-Maybe f p x =
    htpy-eq-equiv
      ( pr1 (pair-eq-Σ (pr2 (pr1 (pr2 extend-equiv-Maybe)) (pair f p))))
      ( inl x)

  comp-extend-equiv-Maybe :
    (f g : type-Set X ≃ type-Set X) →
    htpy-equiv
      ( pr1 (map-equiv extend-equiv-Maybe (f ∘e g)))
      ( ( pr1 (map-equiv extend-equiv-Maybe f)) ∘e
        ( pr1 (map-equiv extend-equiv-Maybe g)))
  comp-extend-equiv-Maybe f g =
    preserves-comp-map-coproduct (map-equiv g) (map-equiv f) id id
```
