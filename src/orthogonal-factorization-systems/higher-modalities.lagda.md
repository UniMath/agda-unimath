# Higher modalities

```agda
module orthogonal-factorization-systems.higher-modalities where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-extensionality-axiom
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.precomposition-dependent-functions
open import foundation.retractions
open import foundation.small-types
open import foundation.transport-along-identifications
open import foundation.univalence
open import foundation.universe-levels

open import orthogonal-factorization-systems.locally-small-modal-operators
open import orthogonal-factorization-systems.modal-induction
open import orthogonal-factorization-systems.modal-operators
open import orthogonal-factorization-systems.modal-subuniverse-induction
open import orthogonal-factorization-systems.uniquely-eliminating-modalities
```

</details>

## Idea

A {{#concept "higher modality" Disambiguation="on types" Agda=higher-modality}}
is a _higher mode of logic_ defined in terms of an monadic
[modal operator](orthogonal-factorization-systems.modal-operators.md) `○`
satisfying a certain induction principle.

The induction principle states that for every type `X` and family `P : ○ X → 𝒰`,
to define a dependent map `(x' : ○ X) → ○ (P x')` it suffices to define it on
the image of the modal unit, i.e. `(x : X) → ○ (P (unit-○ x))`. Moreover, it
satisfies a computation principle stating that when evaluating a map defined in
this manner on the image of the modal unit, one recovers the defining map
(propositionally).

Lastly, higher modalities must also be **identity closed** in the sense that for
every type `X` the identity types `(x' ＝ y')` are modal for all terms
`x' y' : ○ X`. In other words, `○ X` is
[`○`-separated](foundation.separated-types-subuniverses.md). Because of this,
(small) higher modalities in their most general form only make sense for
[locally small modal operators](orthogonal-factorization-systems.locally-small-modal-operators.md).

## Definition

### Closure under identity type formers

We say that the [identity types](foundation-core.identity-types.md) of a
[locally small type](foundation.locally-small-types.md) are **modal** if their
[small equivalent](foundation-core.small-types.md) is modal. We say that a
modality is closed under [identity type](foundation-core.identity-types.md)
formation if, for every modal type, their identity types are also modal.

```agda
module _
  {l1 l2 : Level}
  ((○ , is-locally-small-○) : locally-small-operator-modality l1 l2 l1)
  (unit-○ : unit-modality ○)
  where

  is-modal-small-identity-types : UU (lsuc l1 ⊔ l2)
  is-modal-small-identity-types =
    (X : UU l1) (x y : ○ X) →
    is-modal-type-is-small (unit-○) (x ＝ y) (is-locally-small-○ X x y)
```

### The predicate of being a higher modality

```agda
  is-higher-modality : UU (lsuc l1 ⊔ l2)
  is-higher-modality =
    induction-principle-modality (unit-○) × is-modal-small-identity-types
```

### Components of a higher modality proof

```agda
module _
  {l1 l2 : Level}
  (locally-small-○ : locally-small-operator-modality l1 l2 l1)
  (unit-○ : unit-modality (pr1 locally-small-○))
  (h : is-higher-modality locally-small-○ unit-○)
  where

  induction-principle-is-higher-modality : induction-principle-modality unit-○
  induction-principle-is-higher-modality = pr1 h

  ind-is-higher-modality : ind-modality unit-○
  ind-is-higher-modality =
    ind-induction-principle-modality
      ( unit-○)
      ( induction-principle-is-higher-modality)

  compute-ind-is-higher-modality :
    compute-ind-modality unit-○ ind-is-higher-modality
  compute-ind-is-higher-modality =
    compute-ind-induction-principle-modality
      ( unit-○)
      ( induction-principle-is-higher-modality)

  recursion-principle-is-higher-modality : recursion-principle-modality unit-○
  recursion-principle-is-higher-modality =
    recursion-principle-induction-principle-modality
      ( unit-○)
      ( induction-principle-is-higher-modality)

  rec-is-higher-modality : rec-modality unit-○
  rec-is-higher-modality =
    rec-recursion-principle-modality
      ( unit-○)
      ( recursion-principle-is-higher-modality)

  compute-rec-is-higher-modality :
    compute-rec-modality unit-○ rec-is-higher-modality
  compute-rec-is-higher-modality =
    compute-rec-recursion-principle-modality
      ( unit-○)
      ( recursion-principle-is-higher-modality)

  is-modal-small-identity-types-is-higher-modality :
    is-modal-small-identity-types locally-small-○ unit-○
  is-modal-small-identity-types-is-higher-modality = pr2 h
```

### The structure of a higher modality

```agda
higher-modality : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
higher-modality l1 l2 =
  Σ ( locally-small-operator-modality l1 l2 l1)
    ( λ ○ →
      Σ ( unit-modality (pr1 ○))
        ( is-higher-modality ○))
```

### Components of a higher modality

```agda
module _
  {l1 l2 : Level} (h : higher-modality l1 l2)
  where

  locally-small-operator-higher-modality :
    locally-small-operator-modality l1 l2 l1
  locally-small-operator-higher-modality = pr1 h

  operator-higher-modality : operator-modality l1 l2
  operator-higher-modality =
    operator-modality-locally-small-operator-modality
      ( locally-small-operator-higher-modality)

  is-locally-small-operator-higher-modality :
    is-locally-small-operator-modality l1 (operator-higher-modality)
  is-locally-small-operator-higher-modality =
    is-locally-small-locally-small-operator-modality
      ( locally-small-operator-higher-modality)

  unit-higher-modality :
    unit-modality (operator-higher-modality)
  unit-higher-modality = pr1 (pr2 h)

  is-higher-modality-higher-modality :
    is-higher-modality
      ( locally-small-operator-higher-modality)
      ( unit-higher-modality)
  is-higher-modality-higher-modality = pr2 (pr2 h)

  induction-principle-higher-modality :
    induction-principle-modality (unit-higher-modality)
  induction-principle-higher-modality =
    induction-principle-is-higher-modality
      ( locally-small-operator-higher-modality)
      ( unit-higher-modality)
      ( is-higher-modality-higher-modality)

  ind-higher-modality :
    ind-modality (unit-higher-modality)
  ind-higher-modality =
    ind-induction-principle-modality
      ( unit-higher-modality)
      ( induction-principle-higher-modality)

  compute-ind-higher-modality :
    compute-ind-modality
      ( unit-higher-modality)
      ( ind-higher-modality)
  compute-ind-higher-modality =
    compute-ind-induction-principle-modality
      ( unit-higher-modality)
      ( induction-principle-higher-modality)

  recursion-principle-higher-modality :
    recursion-principle-modality (unit-higher-modality)
  recursion-principle-higher-modality =
    recursion-principle-is-higher-modality
      ( locally-small-operator-higher-modality)
      ( unit-higher-modality)
      ( is-higher-modality-higher-modality)

  rec-higher-modality :
    rec-modality (unit-higher-modality)
  rec-higher-modality =
    rec-recursion-principle-modality
      ( unit-higher-modality)
      ( recursion-principle-higher-modality)

  compute-rec-higher-modality :
    compute-rec-modality (unit-higher-modality) (rec-higher-modality)
  compute-rec-higher-modality =
    compute-rec-recursion-principle-modality
      ( unit-higher-modality)
      ( recursion-principle-higher-modality)

  is-modal-small-identity-type-higher-modality :
    is-modal-small-identity-types
      ( locally-small-operator-higher-modality)
      ( unit-higher-modality)
  is-modal-small-identity-type-higher-modality =
    ( is-modal-small-identity-types-is-higher-modality)
    ( locally-small-operator-higher-modality)
    ( unit-higher-modality)
    ( is-higher-modality-higher-modality)
```

## Properties

### Subuniverse induction for higher modalities

```agda
module _
  {l1 l2 : Level} (m : higher-modality l1 l2)
  where

  strong-ind-subuniverse-higher-modality :
    strong-ind-subuniverse-modality (unit-higher-modality m)
  strong-ind-subuniverse-higher-modality =
    strong-ind-subuniverse-ind-modality
      ( unit-higher-modality m)
      ( ind-higher-modality m)

  compute-strong-ind-subuniverse-higher-modality :
    compute-strong-ind-subuniverse-modality
      ( unit-higher-modality m)
      ( strong-ind-subuniverse-higher-modality)
  compute-strong-ind-subuniverse-higher-modality =
    compute-strong-ind-subuniverse-ind-modality
      ( unit-higher-modality m)
      ( ind-higher-modality m)
      ( compute-ind-higher-modality m)

  ind-subuniverse-higher-modality :
    ind-subuniverse-modality (unit-higher-modality m)
  ind-subuniverse-higher-modality =
    ind-subuniverse-ind-modality
      ( unit-higher-modality m)
      ( ind-higher-modality m)

  compute-ind-subuniverse-higher-modality :
    compute-ind-subuniverse-modality
      ( unit-higher-modality m)
      ( ind-subuniverse-higher-modality)
  compute-ind-subuniverse-higher-modality =
    compute-ind-subuniverse-ind-modality
      ( unit-higher-modality m)
      ( ind-higher-modality m)
      ( compute-ind-higher-modality m)

  strong-rec-subuniverse-higher-modality :
    strong-rec-subuniverse-modality (unit-higher-modality m)
  strong-rec-subuniverse-higher-modality =
    strong-rec-subuniverse-rec-modality
      ( unit-higher-modality m)
      ( rec-higher-modality m)

  compute-strong-rec-subuniverse-higher-modality :
    compute-strong-rec-subuniverse-modality
      ( unit-higher-modality m)
      ( strong-rec-subuniverse-higher-modality)
  compute-strong-rec-subuniverse-higher-modality =
    compute-strong-rec-subuniverse-rec-modality
      ( unit-higher-modality m)
      ( rec-higher-modality m)
      ( compute-rec-higher-modality m)

  rec-subuniverse-higher-modality :
    rec-subuniverse-modality (unit-higher-modality m)
  rec-subuniverse-higher-modality =
    rec-subuniverse-rec-modality
      ( unit-higher-modality m)
      ( rec-higher-modality m)

  compute-rec-subuniverse-higher-modality :
    compute-rec-subuniverse-modality
      ( unit-higher-modality m)
      ( rec-subuniverse-higher-modality)
  compute-rec-subuniverse-higher-modality =
    compute-rec-subuniverse-rec-modality
      ( unit-higher-modality m)
      ( rec-higher-modality m)
      ( compute-rec-higher-modality m)
```

### When `l1 = l2`, the identity types are modal in the usual sense

```agda
map-inv-unit-small-Id-higher-modality :
  {l1 l2 : Level}
  (m : higher-modality l1 l2)
  {X : UU l1} {x' y' : operator-higher-modality m X} →
  ( operator-higher-modality m
    ( type-is-small (is-locally-small-operator-higher-modality m X x' y'))) →
  x' ＝ y'
map-inv-unit-small-Id-higher-modality m {X} {x'} {y'} =
  map-inv-unit-is-modal-type-is-small
    ( unit-higher-modality m)
    ( x' ＝ y')
    ( is-locally-small-operator-higher-modality m X x' y')
    ( is-modal-small-identity-type-higher-modality m X x' y')

module _
  {l : Level} (m : higher-modality l l)
  where

  map-inv-unit-Id-higher-modality :
    {X : UU l} {x' y' : operator-higher-modality m X} →
    operator-higher-modality m (x' ＝ y') → x' ＝ y'
  map-inv-unit-Id-higher-modality {X} {x'} {y'} =
    map-inv-unit-small-Id-higher-modality m ∘
      ( ap-map-ind-modality
        ( unit-higher-modality m)
        ( ind-higher-modality m)
        ( map-equiv-is-small
          ( is-locally-small-operator-higher-modality m X x' y')))

  is-section-unit-Id-higher-modality :
    {X : UU l} {x' y' : operator-higher-modality m X} →
    (map-inv-unit-Id-higher-modality ∘ unit-higher-modality m {x' ＝ y'}) ~ id
  is-section-unit-Id-higher-modality {X} {x'} {y'} p =
    ( ap
      ( map-inv-equiv
        ( equiv-unit-is-modal-type-is-small
          ( unit-higher-modality m)
          ( x' ＝ y')
          ( is-small-x'=y')
          ( is-modal-small-x'=y')))
      ( compute-rec-higher-modality m
        ( unit-higher-modality m ∘ map-equiv-is-small is-small-x'=y')
        ( p))) ∙
    ( htpy-eq
      ( distributive-map-inv-comp-equiv
        ( equiv-is-small is-small-x'=y')
        ( unit-higher-modality m , is-modal-small-x'=y'))
      ( unit-higher-modality m (map-equiv-is-small is-small-x'=y' p))) ∙
    ( ap
      ( map-inv-equiv-is-small is-small-x'=y')
      ( is-retraction-map-inv-is-equiv is-modal-small-x'=y'
        ( map-equiv-is-small is-small-x'=y' p))) ∙
    ( is-retraction-map-inv-equiv-is-small is-small-x'=y' p)
    where
      is-small-x'=y' = is-locally-small-operator-higher-modality m X x' y'
      is-modal-small-x'=y' =
        is-modal-small-identity-type-higher-modality m X x' y'

  retraction-unit-Id-higher-modality :
    {X : UU l} {x' y' : operator-higher-modality m X} →
    retraction (unit-higher-modality m {x' ＝ y'})
  pr1 retraction-unit-Id-higher-modality = map-inv-unit-Id-higher-modality
  pr2 retraction-unit-Id-higher-modality = is-section-unit-Id-higher-modality
```

We get this retraction without applying univalence, so, using strong subuniverse
induction we can generally avoid it. However, we appeal to univalence to get the
full equivalence.

```agda
  is-modal-Id-higher-modality :
    {X : UU l} {x' y' : operator-higher-modality m X} →
    is-modal (unit-higher-modality m) (x' ＝ y')
  is-modal-Id-higher-modality {X} {x'} {y'} =
    tr
      ( is-modal (unit-higher-modality m))
      ( eq-equiv
        ( inv-equiv-is-small
          ( is-locally-small-operator-higher-modality m X x' y')))
      ( is-modal-small-identity-type-higher-modality m X x' y')
```

### Subuniverse induction on identity types

```agda
module _
  {l : Level} (m : higher-modality l l)
  where

  ind-subuniverse-Id-higher-modality :
    {X : UU l} {Y : operator-higher-modality m X → UU l}
    (f g :
      (x' : operator-higher-modality m X) → operator-higher-modality m (Y x')) →
    (f ∘ unit-higher-modality m) ~ (g ∘ unit-higher-modality m) →
    f ~ g
  ind-subuniverse-Id-higher-modality {X} f g =
    strong-ind-subuniverse-higher-modality m
      ( λ x' → f x' ＝ g x')
      ( λ _ → retraction-unit-Id-higher-modality m)

  compute-ind-subuniverse-Id-higher-modality :
    {X : UU l} {Y : operator-higher-modality m X → UU l}
    (f g :
      (x' : operator-higher-modality m X) → operator-higher-modality m (Y x')) →
    (H : (f ∘ unit-higher-modality m) ~ (g ∘ unit-higher-modality m)) →
    (x : X) →
    ( strong-ind-subuniverse-higher-modality m
      ( λ x' → f x' ＝ g x')
      ( λ _ → retraction-unit-Id-higher-modality m)
      ( H)
      ( unit-higher-modality m x)) ＝
    ( H x)
  compute-ind-subuniverse-Id-higher-modality f g =
    compute-strong-ind-subuniverse-higher-modality m
      ( λ x → f x ＝ g x)
      ( λ _ → retraction-unit-Id-higher-modality m)
```

### Types in the image of the modal operator are modal

```agda
module _
  {l : Level} (m : higher-modality l l) (X : UU l)
  where

  map-inv-unit-higher-modality :
    operator-higher-modality m (operator-higher-modality m X) →
    operator-higher-modality m X
  map-inv-unit-higher-modality = rec-higher-modality m id

  is-retraction-map-inv-unit-higher-modality :
    map-inv-unit-higher-modality ∘ unit-higher-modality m ~ id
  is-retraction-map-inv-unit-higher-modality = compute-rec-higher-modality m id

  is-section-map-inv-unit-higher-modality :
    unit-higher-modality m ∘ map-inv-unit-higher-modality ~ id
  is-section-map-inv-unit-higher-modality =
    ind-subuniverse-Id-higher-modality m _ _
      ( ap (unit-higher-modality m) ∘
        is-retraction-map-inv-unit-higher-modality)

  is-modal-operator-type-higher-modality :
    is-modal (unit-higher-modality m) (operator-higher-modality m X)
  is-modal-operator-type-higher-modality =
    is-equiv-is-invertible
      map-inv-unit-higher-modality
      is-section-map-inv-unit-higher-modality
      is-retraction-map-inv-unit-higher-modality
```

### Higher modalities are uniquely eliminating modalities

```agda
is-section-ind-higher-modality :
  {l1 l2 : Level} (m : higher-modality l1 l2)
  {X : UU l1} {P : operator-higher-modality m X → UU l1} →
  ( ( precomp-Π (unit-higher-modality m) (operator-higher-modality m ∘ P)) ∘
    ( ind-higher-modality m P)) ~
  ( id)
is-section-ind-higher-modality m =
  is-section-ind-modality
    ( unit-higher-modality m)
    ( ind-higher-modality m)
    ( compute-ind-higher-modality m)

module _
  {l : Level} (m : higher-modality l l)
  where

  is-retraction-ind-higher-modality :
    {X : UU l} (P : operator-higher-modality m X → UU l) →
    ( ind-higher-modality m P ∘
      precomp-Π (unit-higher-modality m) (operator-higher-modality m ∘ P)) ~
    ( id)
  is-retraction-ind-higher-modality P s =
    eq-htpy
      ( ind-subuniverse-Id-higher-modality m _ _
        ( compute-ind-higher-modality m P (s ∘ unit-higher-modality m)))

  is-equiv-ind-higher-modality :
    {X : UU l} (P : operator-higher-modality m X → UU l) →
    is-equiv (ind-higher-modality m P)
  is-equiv-ind-higher-modality P =
    is-equiv-is-invertible
      ( precomp-Π (unit-higher-modality m) (operator-higher-modality m ∘ P))
      ( is-retraction-ind-higher-modality P)
      ( is-section-ind-higher-modality m)

  equiv-ind-higher-modality :
    {X : UU l} (P : operator-higher-modality m X → UU l) →
    ((x : X) → operator-higher-modality m (P (unit-higher-modality m x))) ≃
    ((x' : operator-higher-modality m X) → operator-higher-modality m (P x'))
  pr1 (equiv-ind-higher-modality P) = ind-higher-modality m P
  pr2 (equiv-ind-higher-modality P) = is-equiv-ind-higher-modality P

  is-uniquely-eliminating-higher-modality :
    is-uniquely-eliminating-modality (unit-higher-modality m)
  is-uniquely-eliminating-higher-modality P =
    is-equiv-map-inv-is-equiv (is-equiv-ind-higher-modality P)
```

## See also

The equivalent notions of

- [Uniquely eliminating modalities](orthogonal-factorization-systems.uniquely-eliminating-modalities.md)
- [Σ-closed reflective modalities](orthogonal-factorization-systems.sigma-closed-reflective-modalities.md)
- [Σ-closed reflective subuniverses](orthogonal-factorization-systems.sigma-closed-reflective-subuniverses.md)
- [Stable orthogonal factorization systems](orthogonal-factorization-systems.stable-orthogonal-factorization-systems.md)

## References

{{#bibliography}} {{#reference RSS20}}
