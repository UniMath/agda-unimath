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
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.small-types
open import foundation.transport
open import foundation.univalence
open import foundation.universe-levels

open import orthogonal-factorization-systems.induction-modalities
open import orthogonal-factorization-systems.locally-small-modal-operators
open import orthogonal-factorization-systems.modal-operators
open import orthogonal-factorization-systems.subuniverse-induction-modalities
open import orthogonal-factorization-systems.uniquely-eliminating-modalities
```

</details>

## Idea

A **higher modality** is a _higher mode of logic_ defined in terms of a monadic
[modal operator](orthogonal-factorization-systems.modal-operators.md) `○`
satisfying a certain induction principle.

The induction principle states that for every type `X` and family
`P : ○ X → UU`, to define a dependent map `(x' : ○ X) → ○ (P x')` it suffices to
define it on the image of the modal unit, i.e. `(x : X) → ○ (P (unit-○ x))`.
Moreover, it satisfies a computation principle stating that when evaluating a
map defined in this manner on the image of the modal unit, one recovers the
defining map (propositionally).

Lastly, higher modalities must also be **identity closed** in the sense that for
every type `X` the identity types `(x' ＝ y')` are modal for all terms
`x' y' : ○ X`. In other words, `○ X` is
[`○`-separated](orthogonal-factorization-systems.separated-types.md). Because of
this, higher modalities in their most general form only make sense for
[locally small modal operators](orthogonal-factorization-systems.locally-small-modal-operators.md).

## Definition

### Closure under identity type formers

We say that the [locally small type](foundation-core.identity-types.md) of a
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

  is-modal-identity-types : UU (lsuc l1 ⊔ l2)
  is-modal-identity-types =
    (X : UU l1) (x y : ○ X) →
    is-modal-type-is-small (unit-○) (x ＝ y) (is-locally-small-○ X x y)
```

### The `is-higher-modality` predicate

```agda
  is-higher-modality : UU (lsuc l1 ⊔ l2)
  is-higher-modality =
    dependent-universal-property-modality (unit-○) × is-modal-identity-types
```

### Components of a `is-higher-modality` proof

```agda
  ind-is-higher-modality : is-higher-modality → ind-modality unit-○
  ind-is-higher-modality = pr1 ∘ pr1

  rec-modality-is-higher-modality : is-higher-modality → rec-modality unit-○
  rec-modality-is-higher-modality =
    rec-ind-modality unit-○ ∘ ind-is-higher-modality

  compute-ind-is-higher-modality :
    (h : is-higher-modality) →
    compute-ind-modality unit-○ (ind-is-higher-modality h)
  compute-ind-is-higher-modality = pr2 ∘ pr1

  is-modal-identity-types-is-higher-modality :
    is-higher-modality → is-modal-identity-types
  is-modal-identity-types-is-higher-modality = pr2
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

  ind-higher-modality :
    ind-modality (unit-higher-modality)
  ind-higher-modality =
    ind-is-higher-modality
      ( locally-small-operator-higher-modality)
      ( unit-higher-modality)
      ( is-higher-modality-higher-modality)

  rec-higher-modality :
    rec-modality (unit-higher-modality)
  rec-higher-modality =
    rec-ind-modality
      ( unit-higher-modality)
      ( ind-higher-modality)

  compute-ind-higher-modality :
    compute-ind-modality
      ( unit-higher-modality)
      ( ind-higher-modality)
  compute-ind-higher-modality =
    compute-ind-is-higher-modality
      ( locally-small-operator-higher-modality)
      ( unit-higher-modality)
      ( is-higher-modality-higher-modality)

  compute-rec-higher-modality :
    compute-rec-modality
      ( unit-higher-modality)
      ( rec-higher-modality)
  compute-rec-higher-modality =
    compute-rec-compute-ind-modality
      ( unit-higher-modality)
      ( ind-higher-modality)
      ( compute-ind-higher-modality)

  is-modal-small-identity-type-higher-modality :
    is-modal-identity-types
      ( locally-small-operator-higher-modality)
      ( unit-higher-modality)
  is-modal-small-identity-type-higher-modality =
    ( is-modal-identity-types-is-higher-modality)
    ( locally-small-operator-higher-modality)
    ( unit-higher-modality)
    ( is-higher-modality-higher-modality)
```

## Properties

### Subuniverse induction and recursion for higher modalities

```agda
module _
  {l1 l2 : Level} (m : higher-modality l1 l2)
  where

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

### Modal induction on identity types

```agda
map-inv-unit-Id-modality :
  {l1 l2 : Level}
  ((○ , is-locally-small-○) : locally-small-operator-modality l1 l2 l1)
  (unit-○ : unit-modality ○)
  (Id-○ : is-modal-identity-types (○ , is-locally-small-○) unit-○)
  {X : UU l1} {x' y' : ○ X} →
  ○ (type-is-small (is-locally-small-○ X x' y')) → x' ＝ y'
map-inv-unit-Id-modality
  (○ , is-locally-small-○) unit-○ Id-○ {X} {x'} {y'} =
  map-inv-unit-is-modal-type-is-small unit-○
    ( x' ＝ y')
    ( is-locally-small-○ X x' y')
    ( Id-○ X x' y')

map-inv-unit-Id-higher-modality' :
  {l1 l2 : Level}
  (m : higher-modality l1 l2)
  {X : UU l1} {x' y' : operator-higher-modality m X} →
  operator-higher-modality m
    ( type-is-small (is-locally-small-operator-higher-modality m X x' y')) →
  x' ＝ y'
map-inv-unit-Id-higher-modality' m =
  map-inv-unit-Id-modality
    ( locally-small-operator-higher-modality m)
    ( unit-higher-modality m)
    ( is-modal-small-identity-type-higher-modality m)

ind-Id-higher-modality' :
  {l1 l2 : Level}
  (m : higher-modality l1 l2)
  (X : UU l1) (Y : operator-higher-modality m X → UU l1)
  (f g :
    (x' : operator-higher-modality m X) → operator-higher-modality m (Y x')) →
  ( (x : X) →
    operator-higher-modality m
      ( type-is-small
        ( is-locally-small-operator-higher-modality m
          ( Y (unit-higher-modality m x))
          ( f (unit-higher-modality m x))
          ( g (unit-higher-modality m x))))) →
  ( x' : operator-higher-modality m X) →
  operator-higher-modality m
    ( type-is-small
      ( is-locally-small-operator-higher-modality m (Y x') (f x') (g x')))
ind-Id-higher-modality' m X Y f g =
  ind-higher-modality m X
    ( λ x' →
      type-is-small
        ( is-locally-small-operator-higher-modality m (Y x') (f x') (g x')))

-- TODO
-- ind-Id-higher-modality :
--   {l l : Level}
--   (m : higher-modality l l)
--   (X : UU l) (Y : operator-higher-modality m X → UU l)
--   (f g :
--     (x' : operator-higher-modality m X) → operator-higher-modality m (Y x')) →
--   ( (x : X) →
--     operator-higher-modality m
--       ( type-is-small
--         ( is-locally-small-operator-higher-modality m
--           ( Y (unit-higher-modality m x))
--           ( f (unit-higher-modality m x))
--           ( g (unit-higher-modality m x))))) →
--   ( x' : operator-higher-modality m X) → {!   !}
-- ind-Id-higher-modality m X Y f g = {!   !}

-- TODO: ind-subuniverse-Id-higher-modality
-- TODO: same for computations
```

### For homogenous higher modalities, The identity types of modal types are modal in the usual sense

Currently, this uses univalence, although it may be possible to avoid it. One
surefire way to do this is if we had given a second definition of higher
modalities when `l1 = l2`.

```agda
module _
  {l : Level} (m : higher-modality l l)
  where

  map-inv-unit-Id-higher-modality :
    {X : UU l} {x' y' : operator-higher-modality m X} →
    operator-higher-modality m (x' ＝ y') → x' ＝ y'
  map-inv-unit-Id-higher-modality {X} {x'} {y'} =
    map-inv-unit-is-modal-type-is-small
      ( unit-higher-modality m)
      ( x' ＝ y')
      ( is-locally-small-operator-higher-modality m X x' y')
      ( is-modal-small-identity-type-higher-modality m X x' y') ∘
      ( map-ind-modality
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
          ( is-small-x=y)
          ( is-modal-x=y)))
      ( compute-ind-higher-modality m
        ( x' ＝ y')
        ( λ _ → type-is-small is-small-x=y)
        ( unit-higher-modality m ∘ map-equiv-is-small is-small-x=y)
        ( p))) ∙
    ( ( htpy-eq
        ( distributive-map-inv-comp-equiv
          ( equiv-is-small is-small-x=y)
          ( unit-higher-modality m , is-modal-x=y))
        ( unit-higher-modality m (map-equiv-is-small is-small-x=y p))) ∙
      ( ( ap
          ( map-inv-equiv-is-small is-small-x=y)
          ( is-retraction-map-inv-is-equiv is-modal-x=y
            ( map-equiv-is-small is-small-x=y p))) ∙
        ( is-retraction-map-inv-equiv (equiv-is-small is-small-x=y) p)))
    where
      is-small-x=y = is-locally-small-operator-higher-modality m X x' y'
      is-modal-x=y = is-modal-small-identity-type-higher-modality m X x' y'

  is-modal-Id-higher-modality :
    {X : UU l} {x' y' : operator-higher-modality m X} →
    is-modal (unit-higher-modality m) (x' ＝ y')
  is-modal-Id-higher-modality {X} {x'} {y'} =
    tr
      ( is-modal (unit-higher-modality m))
      ( eq-equiv
        ( type-is-small (is-locally-small-operator-higher-modality m X x' y'))
        ( x' ＝ y')
        ( inv-equiv-is-small
          ( is-locally-small-operator-higher-modality m X x' y')))
      ( is-modal-small-identity-type-higher-modality m X x' y')
```

### `○ X` is modal

```agda
module _
  {l : Level}
  ( ((○ , is-locally-small-○) , unit-○ , (ind-○ , compute-ind-○) , Id-○) :
      higher-modality l l)
  (X : UU l)
  where

  map-inv-unit-higher-modality : ○ (○ X) → ○ X
  map-inv-unit-higher-modality = ind-○ (○ X) (λ _ → X) id

  is-retraction-map-inv-unit-higher-modality :
    (map-inv-unit-higher-modality ∘ unit-○) ~ id
  is-retraction-map-inv-unit-higher-modality = compute-ind-○ (○ X) (λ _ → X) id

  is-section-map-inv-unit-higher-modality :
    (unit-○ ∘ map-inv-unit-higher-modality) ~ id
  is-section-map-inv-unit-higher-modality x'' =
    map-inv-unit-Id-higher-modality
      ( (○ , is-locally-small-○) , unit-○ , (ind-○ , compute-ind-○) , Id-○)
      ( ind-○ (○ X)
        ( λ x'' → unit-○ (map-inv-unit-higher-modality x'') ＝ x'')
        ( unit-○ ∘ (ap unit-○ ∘ is-retraction-map-inv-unit-higher-modality))
        ( x''))

  is-modal-operator-modality-type : is-modal unit-○ (○ X)
  pr1 (pr1 is-modal-operator-modality-type) = map-inv-unit-higher-modality
  pr2 (pr1 is-modal-operator-modality-type) =
    is-section-map-inv-unit-higher-modality
  pr1 (pr2 is-modal-operator-modality-type) = map-inv-unit-higher-modality
  pr2 (pr2 is-modal-operator-modality-type) =
    is-retraction-map-inv-unit-higher-modality
```

### Higher modalities are uniquely eliminating modalities

```agda
is-section-ind-higher-modality :
  {l1 l2 : Level} (m : higher-modality l1 l2)
  {X : UU l1} {P : operator-higher-modality m X → UU l1} →
  ( ( precomp-Π (unit-higher-modality m) (operator-higher-modality m ∘ P)) ∘
    ( ind-higher-modality m X P)) ~
  ( id)
is-section-ind-higher-modality m =
  is-section-ind-modality
    ( unit-higher-modality m)
    ( ind-higher-modality m)
    ( compute-ind-higher-modality m)

module _
  {l : Level}
  ( ((○ , is-locally-small-○) , unit-○ , (ind-○ , compute-ind-○) , Id-○) :
      higher-modality l l)
  where

  is-retraction-ind-higher-modality :
    {X : UU l} {P : ○ X → UU l} → (ind-○ X P ∘ precomp-Π unit-○ (○ ∘ P)) ~ id
  is-retraction-ind-higher-modality {X} {P} s =
    eq-htpy
      ( map-inv-unit-Id-higher-modality
        ( (○ , is-locally-small-○) , unit-○ , (ind-○ , compute-ind-○) , Id-○) ∘
        ( ind-○ X
          ( λ x' → (ind-○ X P ∘ precomp-Π (unit-○) (○ ∘ P)) s x' ＝ s x')
          ( unit-○ ∘ compute-ind-○ X P (s ∘ unit-○))))

  is-equiv-ind-higher-modality :
    (X : UU l) (P : ○ X → UU l) → is-equiv (ind-○ X P)
  pr1 (pr1 (is-equiv-ind-higher-modality X P)) = precomp-Π unit-○ (○ ∘ P)
  pr2 (pr1 (is-equiv-ind-higher-modality X P)) =
    is-retraction-ind-higher-modality
  pr1 (pr2 (is-equiv-ind-higher-modality X P)) = precomp-Π unit-○ (○ ∘ P)
  pr2 (pr2 (is-equiv-ind-higher-modality X P)) =
    is-section-ind-higher-modality
      ( (○ , is-locally-small-○) , unit-○ , (ind-○ , compute-ind-○) , Id-○)

  equiv-ind-higher-modality :
    (X : UU l) (P : ○ X → UU l) →
    ((x : X) → ○ (P (unit-○ x))) ≃ ((x' : ○ X) → ○ (P x'))
  pr1 (equiv-ind-higher-modality X P) = ind-○ X P
  pr2 (equiv-ind-higher-modality X P) = is-equiv-ind-higher-modality X P

  is-uniquely-eliminating-higher-modality :
    is-uniquely-eliminating-modality unit-○
  is-uniquely-eliminating-higher-modality X P =
    is-equiv-map-inv-is-equiv (is-equiv-ind-higher-modality X P)
```

## See also

The equivalent notions of

- [Uniquely eliminating modalities](orthogonal-factorization-systems.uniquely-eliminating-modalities.md)
- [Σ-closed reflective modalities](orthogonal-factorization-systems.sigma-closed-reflective-modalities.md)
- [Σ-closed reflective subuniverses](orthogonal-factorization-systems.sigma-closed-reflective-subuniverses.md)
- [Stable orthogonal factorization systems](orthogonal-factorization-systems.stable-orthogonal-factorization-systems.md)

## References

- Egbert Rijke, Michael Shulman, Bas Spitters, _Modalities in homotopy type
  theory_, Logical Methods in Computer Science, Volume 16, Issue 1, 2020
  ([arXiv:1706.07526](https://arxiv.org/abs/1706.07526),
  [doi:10.23638](https://doi.org/10.23638/LMCS-16%281%3A2%292020))
