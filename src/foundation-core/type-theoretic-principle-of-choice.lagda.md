# The type theoretic principle of choice

```agda
module foundation-core.type-theoretic-principle-of-choice where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
```

</details>

## Idea

A dependent function taking values in a
[dependent pair type](foundation.dependent-pair-types.md) is
[equivalently](foundation-core.equivalences.md) described as a pair of dependent
functions. This equivalence, which gives the distributivity of Π over Σ, is also
known as the **type theoretic principle of choice**. Indeed, it is the
Curry-Howard interpretation of (one formulation of) the
[axiom of choice](foundation.axiom-of-choice.md).

We establish this equivalence both for explicit and implicit function types.

## Definitions

### Dependent products of dependent pair types

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

### Implicit dependent products of dependent pair types

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

## Theorem

### The distributivity of Π over Σ

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
  is-section-map-inv-distributive-Π-Σ (ψ , ψ') = refl

  is-retraction-map-inv-distributive-Π-Σ :
    map-inv-distributive-Π-Σ ∘ map-distributive-Π-Σ ~ id
  is-retraction-map-inv-distributive-Π-Σ φ = refl

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

### The distributivity of implicit Π over Σ

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
  pr1 (map-inv-distributive-implicit-Π-Σ ψ {x}) = pr1 ψ
  pr2 (map-inv-distributive-implicit-Π-Σ ψ {x}) = pr2 ψ

  is-section-map-inv-distributive-implicit-Π-Σ :
    ( ( map-distributive-implicit-Π-Σ) ∘
      ( map-inv-distributive-implicit-Π-Σ)) ~ id
  is-section-map-inv-distributive-implicit-Π-Σ (ψ , ψ') = refl

  is-retraction-map-inv-distributive-implicit-Π-Σ :
    ( ( map-inv-distributive-implicit-Π-Σ) ∘
      ( map-distributive-implicit-Π-Σ)) ~ id
  is-retraction-map-inv-distributive-implicit-Π-Σ φ = refl

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

### Ordinary functions into a Σ-type

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : B → UU l3}
  where

  mapping-into-Σ : (A → Σ B C) → Σ (A → B) (λ f → (x : A) → C (f x))
  mapping-into-Σ = map-distributive-Π-Σ {B = λ _ → B}

  abstract
    is-equiv-mapping-into-Σ : is-equiv mapping-into-Σ
    is-equiv-mapping-into-Σ = is-equiv-map-distributive-Π-Σ

  equiv-mapping-into-Σ :
    (A → Σ B C) ≃ Σ (A → B) (λ f → (x : A) → C (f x))
  pr1 equiv-mapping-into-Σ = mapping-into-Σ
  pr2 equiv-mapping-into-Σ = is-equiv-mapping-into-Σ
```
