# The parametricity axiom

```agda
module foundation.parametricity-axiom where
```

<details><summary>Imports</summary>

```agda
open import foundation.axiom-of-choice
open import foundation.booleans
open import foundation.constant-maps
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.diaconescus-theorem
open import foundation.empty-types
open import foundation.evaluation-functions
open import foundation.function-extensionality
open import foundation.law-of-excluded-middle
open import foundation.mere-equality
open import foundation.parametric-types
open import foundation.reflecting-maps-equivalence-relations
open import foundation.retracts-of-types
open import foundation.sets
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.unit-type
open import foundation.universal-property-equivalences
open import foundation.universal-property-set-quotients
open import foundation.universe-levels

open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.negation
open import foundation-core.propositions
open import foundation-core.type-theoretic-principle-of-choice

open import orthogonal-factorization-systems.null-types
```

</details>

## Idea

The {{#concept "parametricity axiom" Agda=Parametricity}} states that all types
are [parametric](foundation.parametric-types.md). I.e., for each type `X : 𝒰`,
the [constant map](foundation.constant-maps.md)

```text
  X → (𝒰 → X)
```

is an [equivalence](foundation-core.equivalences.md).

## Definition

```agda
level-Parametricity : (l : Level) → UU (lsuc l)
level-Parametricity l = {X : UU l} → is-parametric l X

Parametricity : UUω
Parametricity = {l : Level} → level-Parametricity l
```

## Consequences

### Parametricity of booleans contradicts excluded middle

```agda
module _
  {l : Level}
  where abstract

  is-empty-map-bool-LEM : LEM l → UU l → bool
  is-empty-map-bool-LEM lem X =
    rec-coproduct (λ _ → true) (λ _ → false) (lem (is-empty-Prop X))

  compute-is-empty-map-bool-LEM-raise-empty :
    (lem : LEM l) →
    is-empty-map-bool-LEM lem (raise-empty l) ＝ true
  compute-is-empty-map-bool-LEM-raise-empty lem =
    ind-coproduct
      ( λ d → rec-coproduct (λ _ → true) (λ _ → false) d ＝ true)
      ( λ _ → refl)
      ( λ p → ex-falso (p is-empty-raise-empty))
      ( lem (is-empty-Prop (raise-empty l)))

  compute-is-empty-map-bool-LEM-raise-unit :
    (lem : LEM l) →
    is-empty-map-bool-LEM lem (raise-unit l) ＝ false
  compute-is-empty-map-bool-LEM-raise-unit lem =
    ind-coproduct
      ( λ d → rec-coproduct (λ _ → true) (λ _ → false) d ＝ false)
      ( λ p → ex-falso (p raise-star))
      ( λ _ → refl)
      ( lem (is-empty-Prop (raise-unit l)))

  is-constant-map-is-parametric-bool :
    is-parametric l bool →
    (f : UU l → bool) → (X Y : UU l) → f X ＝ f Y
  is-constant-map-is-parametric-bool H f X Y =
    ( inv (htpy-eq (is-section-map-inv-equiv (const (UU l) , H) f) X)) ∙
    ( htpy-eq (is-section-map-inv-equiv (const (UU l) , H) f) Y)

  no-LEM-is-parametric-bool :
    is-parametric l bool → ¬ LEM l
  no-LEM-is-parametric-bool H lem =
    neq-true-false-bool
      ( ( inv (compute-is-empty-map-bool-LEM-raise-empty lem)) ∙
        ( is-constant-map-is-parametric-bool
          ( H)
          ( is-empty-map-bool-LEM lem)
          ( raise-empty l)
          ( raise-unit l)) ∙
        ( compute-is-empty-map-bool-LEM-raise-unit lem))
```

### The levelwise and global parametricity axioms contradict excluded middle

```agda
abstract
  no-LEM-level-Parametricity :
    {l : Level} → level-Parametricity l → ¬ LEM l
  no-LEM-level-Parametricity {l} H =
    no-LEM-is-parametric-bool
      ( is-parametric-equiv (compute-raise-bool l) (H {X = raise-bool l}))

  no-LEM-Parametricity :
    Parametricity → ¬ LEM lzero
  no-LEM-Parametricity H =
    no-LEM-level-Parametricity (H {l = lzero})
```

### Parametricity contradicts the axiom of choice

```agda
abstract
  no-AC0-level-Parametricity :
    {l : Level} → level-Parametricity l → ¬ level-AC0 l l
  no-AC0-level-Parametricity H ac =
    no-LEM-level-Parametricity H (theorem-Diaconescu ac)

  no-AC0-Parametricity :
    Parametricity → AC0 → empty
  no-AC0-Parametricity H ac =
    no-AC0-level-Parametricity
      ( H {l = lzero})
      ( ac {l1 = lzero} {l2 = lzero})
```

## References

{{#bibliography}} {{#reference Lord25}}
