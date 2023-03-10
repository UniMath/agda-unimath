# Coherent H-spaces

```agda
module structured-types.coherent-h-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.functions
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.path-algebra
open import foundation.sections
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.unital-binary-operations
open import foundation.universe-levels

open import foundation-core.endomorphisms

open import group-theory.homomorphisms-semigroups

open import structured-types.h-spaces
open import structured-types.magmas
open import structured-types.pointed-dependent-functions
open import structured-types.pointed-families-of-types
open import structured-types.pointed-maps
open import structured-types.pointed-sections
open import structured-types.pointed-types
```

</details>

## Idea

A coherent H-space is a "wild unital magma", i.e., it is a pointed type equipped with a binary operation for which the base point is a unit, with a coherence law between the left and the right unit laws.

## Definitions

### Unital binary operations on pointed types

```agda
coherent-unit-laws-mul-Pointed-Type :
  {l : Level} (A : Pointed-Type l)
  (μ : (x y : type-Pointed-Type A) → type-Pointed-Type A) → UU l
coherent-unit-laws-mul-Pointed-Type A μ =
  coherent-unit-laws μ (pt-Pointed-Type A)

coherent-unital-mul-Pointed-Type :
  {l : Level} → Pointed-Type l → UU l
coherent-unital-mul-Pointed-Type A =
  Σ ( type-Pointed-Type A → type-Pointed-Type A → type-Pointed-Type A)
    ( coherent-unit-laws-mul-Pointed-Type A)
```

### Coherent H-spaces

```agda
Coherent-H-Space : (l : Level) → UU (lsuc l)
Coherent-H-Space l =
  Σ ( Pointed-Type l) coherent-unital-mul-Pointed-Type

module _
  {l : Level} (M : Coherent-H-Space l)
  where

  pointed-type-Coherent-H-Space : Pointed-Type l
  pointed-type-Coherent-H-Space = pr1 M

  type-Coherent-H-Space : UU l
  type-Coherent-H-Space = type-Pointed-Type pointed-type-Coherent-H-Space

  unit-Coherent-H-Space : type-Coherent-H-Space
  unit-Coherent-H-Space = pt-Pointed-Type pointed-type-Coherent-H-Space

  coherent-unital-mul-Coherent-H-Space :
    coherent-unital-mul-Pointed-Type pointed-type-Coherent-H-Space
  coherent-unital-mul-Coherent-H-Space = pr2 M

  mul-Coherent-H-Space :
    type-Coherent-H-Space → type-Coherent-H-Space → type-Coherent-H-Space
  mul-Coherent-H-Space = pr1 coherent-unital-mul-Coherent-H-Space

  mul-Coherent-H-Space' :
    type-Coherent-H-Space → type-Coherent-H-Space → type-Coherent-H-Space
  mul-Coherent-H-Space' x y = mul-Coherent-H-Space y x

  ap-mul-Coherent-H-Space :
    {a b c d : type-Coherent-H-Space} → Id a b → Id c d →
    Id (mul-Coherent-H-Space a c) (mul-Coherent-H-Space b d)
  ap-mul-Coherent-H-Space p q = ap-binary mul-Coherent-H-Space p q

  magma-Coherent-H-Space : Magma l
  pr1 magma-Coherent-H-Space = type-Coherent-H-Space
  pr2 magma-Coherent-H-Space = mul-Coherent-H-Space

  coherent-unit-laws-mul-Coherent-H-Space :
    coherent-unit-laws mul-Coherent-H-Space unit-Coherent-H-Space
  coherent-unit-laws-mul-Coherent-H-Space =
    pr2 coherent-unital-mul-Coherent-H-Space

  left-unit-law-mul-Coherent-H-Space :
    (x : type-Coherent-H-Space) →
    Id (mul-Coherent-H-Space unit-Coherent-H-Space x) x
  left-unit-law-mul-Coherent-H-Space =
    pr1 coherent-unit-laws-mul-Coherent-H-Space

  right-unit-law-mul-Coherent-H-Space :
    (x : type-Coherent-H-Space) →
    Id (mul-Coherent-H-Space x unit-Coherent-H-Space) x
  right-unit-law-mul-Coherent-H-Space =
    pr1 (pr2 coherent-unit-laws-mul-Coherent-H-Space)

  coh-unit-laws-mul-Coherent-H-Space :
    Id ( left-unit-law-mul-Coherent-H-Space unit-Coherent-H-Space)
       ( right-unit-law-mul-Coherent-H-Space unit-Coherent-H-Space)
  coh-unit-laws-mul-Coherent-H-Space =
    pr2 (pr2 coherent-unit-laws-mul-Coherent-H-Space)
```

## Properties

### Every H-space can be upgraded to a coherent H-space

```agda
coherent-h-space-H-Space :
  {l : Level} → H-Space l → Coherent-H-Space l
pr1 (coherent-h-space-H-Space A) = pointed-type-H-Space A
pr1 (pr2 (coherent-h-space-H-Space A)) = mul-H-Space A
pr2 (pr2 (coherent-h-space-H-Space A)) =
  coherent-unit-laws-unit-laws (mul-H-Space A) (unit-laws-mul-H-Space A)
```

### The type of coherent H-space structures on `A` is equivalent to the type of sections of `ev_pt : (A → A) →* A`.

```agda
module _
  {l : Level} (A : Pointed-Type l)
  where

  pointed-section-ev-pt-Pointed-Type : UU l
  pointed-section-ev-pt-Pointed-Type =
    pointed-section-Pointed-Type
      ( endo-Pointed-Type (type-Pointed-Type A))
      ( A)
      ( pair (ev-pt-Pointed-Type A) refl)

compute-pointed-section-ev-pt-Pointed-Type :
  {l : Level} (A : Pointed-Type l) →
  pointed-section-ev-pt-Pointed-Type A ≃ coherent-unital-mul-Pointed-Type A
compute-pointed-section-ev-pt-Pointed-Type (pair A a) =
  ( equiv-tot
    ( λ μ →
      ( equiv-Σ
        ( λ p →
          Σ ( (x : A) → μ x a ＝ x)
            ( λ q → p a ＝ q a))
        ( equiv-funext)
        ( λ H →
          equiv-tot
            ( λ K →
              ( ( ( equiv-inv (K a) (htpy-eq H a)) ∘e
                  ( equiv-concat' (K a) (ap-ev a H))) ∘e
                ( equiv-concat' (K a) right-unit)) ∘e
              ( equiv-concat' (K a) right-unit)))))) ∘e
  ( assoc-Σ
    ( A → (A → A))
    ( λ μ → μ a ＝ id)
    ( λ μp →
      Σ ( (x : A) → pr1 μp x a ＝ x)
        ( λ H → H a ＝ ( ( ap (λ h → h a) (pr2 μp) ∙ refl) ∙ refl))))

```
