# Pointed equivalences

```agda
module structured-types.pointed-equivalences where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.structure-identity-principle
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.univalence
open import foundation.universe-levels

open import structured-types.pointed-homotopies
open import structured-types.pointed-maps
open import structured-types.pointed-types
```

</details>

## Idea

A pointed equivalence is an equivalence in the category of pointed spaces.
Equivalently, a pointed equivalence is a pointed map of which the underlying
function is an equivalence.

## Definitions

### Pointed equivalences

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  where

  is-equiv-pointed-map : (A →∗ B) → UU (l1 ⊔ l2)
  is-equiv-pointed-map f = is-equiv (map-pointed-map f)

pointed-equiv :
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2) → UU (l1 ⊔ l2)
pointed-equiv A B =
  Σ ( type-Pointed-Type A ≃ type-Pointed-Type B)
    ( λ e → map-equiv e (point-Pointed-Type A) ＝ point-Pointed-Type B)

infix 6 _≃∗_
_≃∗_ = pointed-equiv

compute-pointed-equiv :
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2) →
  (A ≃∗ B) ≃ Σ (A →∗ B) (is-equiv-pointed-map {A = A} {B})
compute-pointed-equiv A B = equiv-right-swap-Σ

module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2} (e : A ≃∗ B)
  where

  equiv-pointed-equiv : type-Pointed-Type A ≃ type-Pointed-Type B
  equiv-pointed-equiv = pr1 e

  map-equiv-pointed-equiv : type-Pointed-Type A → type-Pointed-Type B
  map-equiv-pointed-equiv = map-equiv equiv-pointed-equiv

  is-equiv-map-equiv-pointed-equiv : is-equiv map-equiv-pointed-equiv
  is-equiv-map-equiv-pointed-equiv = is-equiv-map-equiv equiv-pointed-equiv

  preserves-point-equiv-pointed-equiv :
    Id (map-equiv-pointed-equiv (point-Pointed-Type A)) (point-Pointed-Type B)
  preserves-point-equiv-pointed-equiv = pr2 e

  pointed-map-pointed-equiv : A →∗ B
  pr1 pointed-map-pointed-equiv = map-equiv-pointed-equiv
  pr2 pointed-map-pointed-equiv = preserves-point-equiv-pointed-equiv

  is-equiv-pointed-map-pointed-equiv :
    is-equiv-pointed-map pointed-map-pointed-equiv
  is-equiv-pointed-map-pointed-equiv = is-equiv-map-equiv-pointed-equiv
```

### The identity pointed equivalence

```agda
module _
  {l : Level} {A : Pointed-Type l}
  where

  id-pointed-equiv : A ≃∗ A
  pr1 id-pointed-equiv = id-equiv
  pr2 id-pointed-equiv = refl
```

### Composition of pointed equivalences

```agda
module _
  {l1 l2 l3 : Level}
  {A : Pointed-Type l1} {B : Pointed-Type l2} {C : Pointed-Type l3}
  where

  comp-pointed-equiv : (B ≃∗ C) → (A ≃∗ B) → (A ≃∗ C)
  pr1 (comp-pointed-equiv f e) =
    equiv-pointed-equiv f ∘e equiv-pointed-equiv e
  pr2 (comp-pointed-equiv f e) =
    preserves-point-comp-pointed-map
      ( pointed-map-pointed-equiv f)
      ( pointed-map-pointed-equiv e)
```

### Pointed isomorphisms

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2} (f : A →∗ B)
  where

  section-pointed-map : UU (l1 ⊔ l2)
  section-pointed-map = Σ (B →∗ A) (λ g → (f ∘∗ g) ~∗ id-pointed-map)

  retraction-pointed-map : UU (l1 ⊔ l2)
  retraction-pointed-map =
    Σ (B →∗ A) (λ g → (g ∘∗ f) ~∗ id-pointed-map)

  is-iso-pointed-map : UU (l1 ⊔ l2)
  is-iso-pointed-map = section-pointed-map × retraction-pointed-map
```

## Properties

### Extensionality of the universe of pointed types

```agda
module _
  {l1 : Level} (A : Pointed-Type l1)
  where

  is-contr-total-equiv-Pointed-Type :
    is-contr (Σ (Pointed-Type l1) (λ B → A ≃∗ B))
  is-contr-total-equiv-Pointed-Type =
    is-contr-total-Eq-structure
      ( λ X x e → map-equiv e (point-Pointed-Type A) ＝ x)
      ( is-contr-total-equiv (type-Pointed-Type A))
      ( pair (type-Pointed-Type A) id-equiv)
      ( is-contr-total-path (point-Pointed-Type A))

  extensionality-Pointed-Type : (B : Pointed-Type l1) → Id A B ≃ (A ≃∗ B)
  extensionality-Pointed-Type =
    extensionality-Σ
      ( λ b e → Id (map-equiv e (point-Pointed-Type A)) b)
      ( id-equiv)
      ( refl)
      ( λ B → equiv-univalence)
      ( λ a → id-equiv)

  eq-pointed-equiv : (B : Pointed-Type l1) → A ≃∗ B → Id A B
  eq-pointed-equiv B = map-inv-equiv (extensionality-Pointed-Type B)
```

### Being a pointed equivalence is equivalent to being a pointed isomorphism

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2} (f : A →∗ B)
  where

  is-contr-section-is-equiv-pointed-map :
    is-equiv-pointed-map f → is-contr (section-pointed-map f)
  is-contr-section-is-equiv-pointed-map H =
    is-contr-total-Eq-structure
      ( λ g p (G : (map-pointed-map f ∘ g) ~ id) →
        Id
          { A =
            Id
              { A = type-Pointed-Type B}
              ( map-pointed-map f (g (point-Pointed-Type B)))
              ( point-Pointed-Type B)}
          ( G (point-Pointed-Type B))
          ( ( ( ap (map-pointed-map f) p) ∙
              ( preserves-point-pointed-map f)) ∙
            ( refl)))
      ( is-contr-section-is-equiv H)
      ( pair (map-inv-is-equiv H) (is-section-map-inv-is-equiv H))
      ( is-contr-equiv
        ( fiber
          ( ap (map-pointed-map f))
          ( ( is-section-map-inv-is-equiv H (point-Pointed-Type B)) ∙
            ( inv (preserves-point-pointed-map f))))
        ( equiv-tot
          ( λ p →
            ( ( equiv-right-transpose-eq-concat
                ( ap (map-pointed-map f) p)
                ( preserves-point-pointed-map f)
                ( is-section-map-inv-is-equiv H (point-Pointed-Type B))) ∘e
              ( equiv-inv
                ( is-section-map-inv-is-equiv H (point-Pointed-Type B))
                ( ( ap (map-pointed-map f) p) ∙
                  ( preserves-point-pointed-map f)))) ∘e
            ( equiv-concat'
              ( is-section-map-inv-is-equiv H (point-Pointed-Type B))
              ( right-unit))))
        ( is-contr-map-is-equiv
          ( is-emb-is-equiv H
            ( map-inv-is-equiv H (point-Pointed-Type B))
            ( point-Pointed-Type A))
          ( ( is-section-map-inv-is-equiv H (point-Pointed-Type B)) ∙
            ( inv (preserves-point-pointed-map f)))))

  is-contr-retraction-is-equiv-pointed-map :
    is-equiv-pointed-map f → is-contr (retraction-pointed-map f)
  is-contr-retraction-is-equiv-pointed-map H =
    is-contr-total-Eq-structure
      ( λ g p (G : (g ∘ map-pointed-map f) ~ id) →
        Id
          { A =
            Id
              { A = type-Pointed-Type A}
              ( g (map-pointed-map f (point-Pointed-Type A)))
              ( point-Pointed-Type A)}
          ( G (point-Pointed-Type A))
          ( ( ( ap g (preserves-point-pointed-map f)) ∙
              ( p)) ∙
            ( refl)))
      ( is-contr-retraction-is-equiv H)
      ( pair (map-inv-is-equiv H) (is-retraction-map-inv-is-equiv H))
      ( is-contr-equiv
        ( fiber
          ( λ p →
            ( ( ap
                ( map-inv-is-equiv H)
                ( preserves-point-pointed-map f)) ∙
              ( p)) ∙
            ( refl))
          ( is-retraction-map-inv-is-equiv H (point-Pointed-Type A)))
        ( equiv-tot (λ p → equiv-inv _ _))
        ( is-contr-map-is-equiv
          ( is-equiv-comp
            ( λ q → q ∙ refl)
            ( λ p →
              ( ap
                ( map-inv-is-equiv H)
                ( preserves-point-pointed-map f)) ∙
              ( p))
            ( is-equiv-concat
              ( ap
                ( map-inv-is-equiv H)
                ( preserves-point-pointed-map f))
              ( point-Pointed-Type A))
            ( is-equiv-concat'
              ( map-inv-is-equiv
                ( H)
                ( map-pointed-map f (point-Pointed-Type A)))
              ( refl)))
          ( is-retraction-map-inv-is-equiv H (point-Pointed-Type A))))

  is-contr-is-iso-is-equiv-pointed-map :
    is-equiv-pointed-map f → is-contr (is-iso-pointed-map f)
  is-contr-is-iso-is-equiv-pointed-map H =
    is-contr-prod
      ( is-contr-section-is-equiv-pointed-map H)
      ( is-contr-retraction-is-equiv-pointed-map H)

  is-iso-is-equiv-pointed-map :
    is-equiv-pointed-map f → is-iso-pointed-map f
  is-iso-is-equiv-pointed-map H =
    center (is-contr-is-iso-is-equiv-pointed-map H)

  is-equiv-is-iso-pointed-map :
    is-iso-pointed-map f → is-equiv-pointed-map f
  pr1 (pr1 (is-equiv-is-iso-pointed-map H)) = pr1 (pr1 (pr1 H))
  pr2 (pr1 (is-equiv-is-iso-pointed-map H)) = pr1 (pr2 (pr1 H))
  pr1 (pr2 (is-equiv-is-iso-pointed-map H)) = pr1 (pr1 (pr2 H))
  pr2 (pr2 (is-equiv-is-iso-pointed-map H)) = pr1 (pr2 (pr2 H))

  is-prop-is-iso-pointed-map : is-prop (is-iso-pointed-map f)
  is-prop-is-iso-pointed-map =
    is-prop-is-proof-irrelevant
      ( λ H →
        is-contr-is-iso-is-equiv-pointed-map (is-equiv-is-iso-pointed-map H))

  equiv-is-iso-is-equiv-pointed-map :
    is-equiv-pointed-map f ≃ (is-iso-pointed-map f)
  pr1 equiv-is-iso-is-equiv-pointed-map = is-iso-is-equiv-pointed-map
  pr2 equiv-is-iso-is-equiv-pointed-map =
    is-equiv-is-prop
      ( is-property-is-equiv (map-pointed-map f))
      ( is-prop-is-iso-pointed-map)
      ( is-equiv-is-iso-pointed-map)
```

### Precomposing by pointed equivalences is a pointed equivalence

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2} (f : A →∗ B)
  where

  is-equiv-is-equiv-precomp-pointed-map :
    ( {l : Level} (C : Pointed-Type l) →
      is-equiv (precomp-pointed-map C f)) →
    is-equiv-pointed-map f
  is-equiv-is-equiv-precomp-pointed-map H =
    is-equiv-is-invertible
      ( map-pointed-map g)
      ( htpy-eq
        ( ap pr1
          ( ap pr1
            ( eq-is-contr
              ( is-contr-map-is-equiv (H B) f)
              { pair
                ( f ∘∗ g)
                ( eq-htpy-pointed-map
                  ( ( f ∘∗ g) ∘∗ f)
                  ( f)
                  ( concat-htpy-pointed-map
                    ( ( f ∘∗ g) ∘∗ f)
                    ( f ∘∗ (g ∘∗ f))
                    ( f)
                    ( associative-comp-pointed-map f g f)
                    ( concat-htpy-pointed-map
                      ( f ∘∗ (g ∘∗ f))
                      ( f ∘∗ id-pointed-map)
                      ( f)
                      ( left-whisker-htpy-pointed-map f
                        ( g ∘∗ f)
                        ( id-pointed-map)
                        ( G))
                      ( right-unit-law-comp-pointed-map f))))}
              { pair
                ( id-pointed-map)
                ( eq-htpy-pointed-map
                  ( id-pointed-map ∘∗ f)
                  ( f)
                  ( left-unit-law-comp-pointed-map f))}))))
      ( pr1 G)
    where
    g : B →∗ A
    g = pr1 (center (is-contr-map-is-equiv (H A) id-pointed-map))
    G : (g ∘∗ f) ~∗ id-pointed-map
    G = map-equiv
          ( extensionality-pointed-map
            ( g ∘∗ f)
            ( id-pointed-map))
          ( pr2 (center (is-contr-map-is-equiv (H A) id-pointed-map)))

  is-equiv-precomp-is-equiv-pointed-map :
    is-equiv-pointed-map f →
    {l : Level} → (C : Pointed-Type l) → is-equiv (precomp-pointed-map C f)
  is-equiv-precomp-is-equiv-pointed-map E C =
    pair
      ( pair
        ( precomp-pointed-map C h)
        ( λ k →
          eq-htpy-pointed-map
            ( (k ∘∗ h) ∘∗ f)
            ( k)
            ( concat-htpy-pointed-map
              ( (k ∘∗ h) ∘∗ f)
              ( k ∘∗ (h ∘∗ f))
              ( k)
              ( associative-comp-pointed-map k h f)
              ( concat-htpy-pointed-map
                ( k ∘∗ (h ∘∗ f))
                ( k ∘∗ id-pointed-map)
                ( k)
                ( left-whisker-htpy-pointed-map k
                  ( h ∘∗ f)
                  ( id-pointed-map)
                  ( H))
                ( right-unit-law-comp-pointed-map k)))))
      ( pair
        ( precomp-pointed-map C g)
        ( λ k →
          eq-htpy-pointed-map
            ( (k ∘∗ f) ∘∗ g)
            ( k)
            ( concat-htpy-pointed-map
              ( (k ∘∗ f) ∘∗ g)
              ( k ∘∗ (f ∘∗ g))
              ( k)
              ( associative-comp-pointed-map k f g)
              ( concat-htpy-pointed-map
                ( k ∘∗ (f ∘∗ g))
                ( k ∘∗ id-pointed-map)
                ( k)
                ( left-whisker-htpy-pointed-map k
                  ( f ∘∗ g)
                  ( id-pointed-map)
                  ( G))
                ( right-unit-law-comp-pointed-map k)))))
    where
    I : is-iso-pointed-map f
    I = is-iso-is-equiv-pointed-map f E
    g : B →∗ A
    g = pr1 (pr1 I)
    G : (f ∘∗ g) ~∗ id-pointed-map
    G = pr2 (pr1 I)
    h : B →∗ A
    h = pr1 (pr2 I)
    H : (h ∘∗ f) ~∗ id-pointed-map
    H = pr2 (pr2 I)

equiv-precomp-pointed-map :
  {l1 l2 l3 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  (C : Pointed-Type l3) → (A ≃∗ B) → (B →∗ C) ≃ (A →∗ C)
pr1 (equiv-precomp-pointed-map C f) g =
  g ∘∗ (pointed-map-pointed-equiv f)
pr2 (equiv-precomp-pointed-map C f) =
  is-equiv-precomp-is-equiv-pointed-map
    ( pointed-map-pointed-equiv f)
    ( is-equiv-map-equiv-pointed-equiv f)
    ( C)
```

### Postcomposing by pointed equivalences is a pointed equivalence

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2} (f : A →∗ B)
  where

  is-equiv-is-equiv-comp-pointed-map :
    ({l : Level} (X : Pointed-Type l) →
    is-equiv (comp-pointed-map {A = X} f)) → is-equiv-pointed-map f
  is-equiv-is-equiv-comp-pointed-map H =
    is-equiv-is-invertible
      ( map-pointed-map g)
      ( pr1 G)
      ( htpy-eq
        ( ap pr1
          ( ap pr1
            ( eq-is-contr
              ( is-contr-map-is-equiv (H A) f)
                { pair
                  ( g ∘∗ f)
                  ( eq-htpy-pointed-map
                    ( f ∘∗ (g ∘∗ f))
                    ( f)
                    ( concat-htpy-pointed-map
                      ( f ∘∗ (g ∘∗ f))
                      ( (f ∘∗ g) ∘∗ f)
                      ( f)
                      ( inv-associative-comp-pointed-map f g f)
                      ( concat-htpy-pointed-map
                        ( (f ∘∗ g) ∘∗ f)
                        ( id-pointed-map ∘∗ f)
                        ( f)
                        ( right-whisker-htpy-pointed-map
                          ( f ∘∗ g)
                          ( id-pointed-map)
                          ( G)
                          ( f))
                        ( left-unit-law-comp-pointed-map f))))}
                { pair
                  ( id-pointed-map)
                  ( eq-htpy-pointed-map
                    ( f ∘∗ id-pointed-map)
                    ( f)
                    ( right-unit-law-comp-pointed-map f))}))))
    where
    g : B →∗ A
    g = pr1 (center (is-contr-map-is-equiv (H B) id-pointed-map))
    G : (f ∘∗ g) ~∗ id-pointed-map
    G = map-equiv
          ( extensionality-pointed-map
            ( f ∘∗ g)
            ( id-pointed-map))
        ( pr2 (center (is-contr-map-is-equiv (H B) id-pointed-map)))

  is-equiv-comp-is-equiv-pointed-map :
    is-equiv-pointed-map f →
    {l : Level} (X : Pointed-Type l) → is-equiv (comp-pointed-map {A = X} f)
  is-equiv-comp-is-equiv-pointed-map E X =
    pair
      ( pair
        ( g ∘∗_)
        ( λ k →
          eq-htpy-pointed-map
            ( f ∘∗ (g ∘∗ k))
            ( k)
            ( concat-htpy-pointed-map
              ( f ∘∗ (g ∘∗ k))
              ( (f ∘∗ g) ∘∗ k)
              ( k)
              ( inv-associative-comp-pointed-map f g k)
              ( concat-htpy-pointed-map
                ( (f ∘∗ g) ∘∗ k)
                ( id-pointed-map ∘∗ k)
                ( k)
                ( right-whisker-htpy-pointed-map
                  ( f ∘∗ g)
                  ( id-pointed-map)
                  ( G)
                  ( k))
                ( left-unit-law-comp-pointed-map k)))))
      ( pair
        ( h ∘∗_)
        ( λ k →
          eq-htpy-pointed-map
            ( h ∘∗ (f ∘∗ k))
            ( k)
            ( concat-htpy-pointed-map
              ( h ∘∗ (f ∘∗ k))
              ( (h ∘∗ f) ∘∗ k)
              ( k)
              ( inv-associative-comp-pointed-map h f k)
              ( concat-htpy-pointed-map
                ( (h ∘∗ f) ∘∗ k)
                ( id-pointed-map ∘∗ k)
                ( k)
                ( right-whisker-htpy-pointed-map
                  ( h ∘∗ f)
                  ( id-pointed-map)
                  ( H)
                  ( k))
                ( left-unit-law-comp-pointed-map k)))))
    where
    I : is-iso-pointed-map f
    I = is-iso-is-equiv-pointed-map f E
    g : B →∗ A
    g = pr1 (pr1 I)
    G : (f ∘∗ g) ~∗ id-pointed-map
    G = pr2 (pr1 I)
    h : B →∗ A
    h = pr1 (pr2 I)
    H : (h ∘∗ f) ~∗ id-pointed-map
    H = pr2 (pr2 I)
```
