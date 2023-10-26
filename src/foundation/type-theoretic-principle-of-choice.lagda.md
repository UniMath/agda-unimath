# The type theoretic principle of choice

```agda
module foundation.type-theoretic-principle-of-choice where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.structure-identity-principle
open import foundation.universe-levels

open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.transport-along-identifications
```

</details>

## Idea

A dependent function taking values in a dependent pair type is equivalently
described as a pair of dependent functions. This equivalence, which gives the
distributivity of Π over Σ, is also known as the type theoretic principle of
choice. Indeed, it is the Curry-Howard interpretation of (one formulation of)
the axiom of choice.

## Distributivity of Π over Σ

### Definitions

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (C : (x : A) → B x → UU l3)
  where

  Π-total-fam : UU (l1 ⊔ l2 ⊔ l3)
  Π-total-fam = (x : A) → Σ (B x) (C x)

  universally-structured-Π : UU (l1 ⊔ l2 ⊔ l3)
  universally-structured-Π = Σ ((x : A) → B x) (λ f → (x : A) → C x (f x))
```

### Properties

#### Characterizing the identity type of `universally-structured-Π`

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
  where

  htpy-universally-structured-Π :
    (t t' : universally-structured-Π C) → UU (l1 ⊔ l2 ⊔ l3)
  htpy-universally-structured-Π t t' =
    universally-structured-Π
      ( λ (x : A) (p : (pr1 t) x ＝ (pr1 t') x) →
        tr (C x) p ((pr2 t) x) ＝ (pr2 t') x)

  extensionality-universally-structured-Π :
    (t t' : universally-structured-Π C) →
    (t ＝ t') ≃ htpy-universally-structured-Π t t'
  extensionality-universally-structured-Π (pair f g) =
    extensionality-Σ
      ( λ {f'} g' (H : f ~ f') → (x : A) → tr (C x) (H x) (g x) ＝ g' x)
      ( refl-htpy)
      ( refl-htpy)
      ( λ f' → equiv-funext)
      ( λ g' → equiv-funext)

  eq-htpy-universally-structured-Π :
    {t t' : universally-structured-Π C} →
    htpy-universally-structured-Π t t' → t ＝ t'
  eq-htpy-universally-structured-Π {t} {t'} =
    map-inv-equiv (extensionality-universally-structured-Π t t')
```

#### The distributivity of Π over Σ

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3}
  where

  map-distributive-Π-Σ : Π-total-fam C → universally-structured-Π C
  pr1 (map-distributive-Π-Σ φ) x = pr1 (φ x)
  pr2 (map-distributive-Π-Σ φ) x = pr2 (φ x)

  map-inv-distributive-Π-Σ : universally-structured-Π C → Π-total-fam C
  pr1 (map-inv-distributive-Π-Σ ψ x) = (pr1 ψ) x
  pr2 (map-inv-distributive-Π-Σ ψ x) = (pr2 ψ) x

  is-section-map-inv-distributive-Π-Σ :
    map-distributive-Π-Σ ∘ map-inv-distributive-Π-Σ ~ id
  is-section-map-inv-distributive-Π-Σ (pair ψ ψ') =
    eq-htpy-universally-structured-Π C (pair refl-htpy refl-htpy)

  is-retraction-map-inv-distributive-Π-Σ :
    map-inv-distributive-Π-Σ ∘ map-distributive-Π-Σ ~ id
  is-retraction-map-inv-distributive-Π-Σ φ =
    eq-htpy (λ x → eq-pair-Σ refl refl)

  abstract
    is-equiv-map-distributive-Π-Σ : is-equiv (map-distributive-Π-Σ)
    is-equiv-map-distributive-Π-Σ =
      is-equiv-is-invertible
        ( map-inv-distributive-Π-Σ)
        ( is-section-map-inv-distributive-Π-Σ)
        ( is-retraction-map-inv-distributive-Π-Σ)

  distributive-Π-Σ : Π-total-fam C ≃ universally-structured-Π C
  pr1 distributive-Π-Σ = map-distributive-Π-Σ
  pr2 distributive-Π-Σ = is-equiv-map-distributive-Π-Σ

  abstract
    is-equiv-map-inv-distributive-Π-Σ : is-equiv (map-inv-distributive-Π-Σ)
    is-equiv-map-inv-distributive-Π-Σ =
      is-equiv-is-invertible
        ( map-distributive-Π-Σ)
        ( is-retraction-map-inv-distributive-Π-Σ)
        ( is-section-map-inv-distributive-Π-Σ)

  inv-distributive-Π-Σ : universally-structured-Π C ≃ Π-total-fam C
  pr1 inv-distributive-Π-Σ = map-inv-distributive-Π-Σ
  pr2 inv-distributive-Π-Σ = is-equiv-map-inv-distributive-Π-Σ
```

### Consequences

#### Characterizing the identity type of `Π-total-fam`

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
  (f g : (a : A) → Σ (B a) (C a))
  where

  Eq-Π-total-fam : UU (l1 ⊔ l2 ⊔ l3)
  Eq-Π-total-fam =
    Π-total-fam (λ x (p : pr1 (f x) ＝ pr1 (g x)) →
      tr (C x) p (pr2 (f x)) ＝ pr2 (g x))

  extensionality-Π-total-fam : (f ＝ g) ≃ Eq-Π-total-fam
  extensionality-Π-total-fam =
    ( inv-distributive-Π-Σ) ∘e
    ( extensionality-universally-structured-Π C
      ( map-distributive-Π-Σ f)
      ( map-distributive-Π-Σ g)) ∘e
    ( equiv-ap distributive-Π-Σ f g)

  eq-Eq-Π-total-fam : Eq-Π-total-fam → f ＝ g
  eq-Eq-Π-total-fam = map-inv-equiv extensionality-Π-total-fam
```

#### Ordinary functions into a Σ-type

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : B → UU l3}
  where

  mapping-into-Σ :
    (A → Σ B C) → Σ (A → B) (λ f → (x : A) → C (f x))
  mapping-into-Σ = map-distributive-Π-Σ {B = λ _ → B}

  abstract
    is-equiv-mapping-into-Σ : is-equiv mapping-into-Σ
    is-equiv-mapping-into-Σ = is-equiv-map-distributive-Π-Σ

  equiv-mapping-into-Σ :
    (A → Σ B C) ≃ Σ (A → B) (λ f → (x : A) → C (f x))
  pr1 equiv-mapping-into-Σ = mapping-into-Σ
  pr2 equiv-mapping-into-Σ = is-equiv-mapping-into-Σ
```

## Distributivity of implicit Π over Σ

### Definitions

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (C : (x : A) → B x → UU l3)
  where

  implicit-Π-total-fam : UU (l1 ⊔ l2 ⊔ l3)
  implicit-Π-total-fam = {x : A} → Σ (B x) (C x)

  universally-structured-implicit-Π : UU (l1 ⊔ l2 ⊔ l3)
  universally-structured-implicit-Π =
    Σ ({x : A} → B x) (λ f → {x : A} → C x (f {x}))
```

### Properties

#### Characterizing the identity type of `universally-structured-implicit-Π`

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
  where

  htpy-universally-structured-implicit-Π :
    (t t' : universally-structured-implicit-Π C) → UU (l1 ⊔ l2 ⊔ l3)
  htpy-universally-structured-implicit-Π t t' =
    universally-structured-Π
      ( λ (x : A) (p : (pr1 t) {x} ＝ (pr1 t') {x}) →
        tr (C x) p ((pr2 t) {x}) ＝ (pr2 t') {x})

  extensionality-universally-structured-implicit-Π :
    (t t' : universally-structured-implicit-Π C) →
    (t ＝ t') ≃ htpy-universally-structured-implicit-Π t t'
  extensionality-universally-structured-implicit-Π (pair f g) =
    extensionality-Σ
      ( λ {f'} g' H → (x : A) → tr (C x) (H x) (g {x}) ＝ g' {x})
      ( refl-htpy)
      ( refl-htpy)
      ( λ f' → equiv-funext-implicit)
      ( λ g' → equiv-funext-implicit)

  eq-htpy-universally-structured-implicit-Π :
    {t t' : universally-structured-implicit-Π C} →
    htpy-universally-structured-implicit-Π t t' → t ＝ t'
  eq-htpy-universally-structured-implicit-Π {t} {t'} =
    map-inv-equiv (extensionality-universally-structured-implicit-Π t t')
```

#### The distributivity of implicit Π over Σ

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3}
  where

  map-distributive-implicit-Π-Σ :
    implicit-Π-total-fam C → universally-structured-implicit-Π C
  pr1 (map-distributive-implicit-Π-Σ φ) {x} = pr1 (φ {x})
  pr2 (map-distributive-implicit-Π-Σ φ) {x} = pr2 (φ {x})

  map-inv-distributive-implicit-Π-Σ :
    universally-structured-implicit-Π C → implicit-Π-total-fam C
  pr1 (map-inv-distributive-implicit-Π-Σ ψ {x}) = (pr1 ψ) {x}
  pr2 (map-inv-distributive-implicit-Π-Σ ψ {x}) = (pr2 ψ) {x}

  is-section-map-inv-distributive-implicit-Π-Σ :
    ( ( map-distributive-implicit-Π-Σ) ∘
      ( map-inv-distributive-implicit-Π-Σ)) ~ id
  is-section-map-inv-distributive-implicit-Π-Σ (pair ψ ψ') =
    eq-htpy-universally-structured-implicit-Π C (pair refl-htpy refl-htpy)

  is-retraction-map-inv-distributive-implicit-Π-Σ :
    ( ( map-inv-distributive-implicit-Π-Σ) ∘
      ( map-distributive-implicit-Π-Σ)) ~ id
  is-retraction-map-inv-distributive-implicit-Π-Σ φ =
    eq-htpy-implicit (λ x → eq-pair-Σ refl refl)

  abstract
    is-equiv-map-distributive-implicit-Π-Σ :
      is-equiv (map-distributive-implicit-Π-Σ)
    is-equiv-map-distributive-implicit-Π-Σ =
      is-equiv-is-invertible
        ( map-inv-distributive-implicit-Π-Σ)
        ( is-section-map-inv-distributive-implicit-Π-Σ)
        ( is-retraction-map-inv-distributive-implicit-Π-Σ)

  distributive-implicit-Π-Σ :
    implicit-Π-total-fam C ≃ universally-structured-implicit-Π C
  pr1 distributive-implicit-Π-Σ = map-distributive-implicit-Π-Σ
  pr2 distributive-implicit-Π-Σ = is-equiv-map-distributive-implicit-Π-Σ

  abstract
    is-equiv-map-inv-distributive-implicit-Π-Σ :
      is-equiv (map-inv-distributive-implicit-Π-Σ)
    is-equiv-map-inv-distributive-implicit-Π-Σ =
      is-equiv-is-invertible
        ( map-distributive-implicit-Π-Σ)
        ( is-retraction-map-inv-distributive-implicit-Π-Σ)
        ( is-section-map-inv-distributive-implicit-Π-Σ)

  inv-distributive-implicit-Π-Σ :
    (universally-structured-implicit-Π C) ≃ (implicit-Π-total-fam C)
  pr1 inv-distributive-implicit-Π-Σ = map-inv-distributive-implicit-Π-Σ
  pr2 inv-distributive-implicit-Π-Σ = is-equiv-map-inv-distributive-implicit-Π-Σ
```
