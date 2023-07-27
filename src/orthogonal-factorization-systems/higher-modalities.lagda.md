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
open import foundation.universe-levels

open import orthogonal-factorization-systems.locally-small-modal-operators
open import orthogonal-factorization-systems.modal-operators
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

### The universal property of higher modalities

```agda
module _
  {l1 l2 : Level}
  {○ : operator-modality l1 l2}
  (unit-○ : unit-modality ○)
  where

  ind-modality : UU (lsuc l1 ⊔ l2)
  ind-modality =
    (X : UU l1) (P : ○ X → UU l1) →
    ((x : X) → ○ (P (unit-○ x))) →
    (x' : ○ X) → ○ (P x')

  rec-modality : UU (lsuc l1 ⊔ l2)
  rec-modality = (X Y : UU l1) → (X → ○ Y) → ○ X → ○ Y

  compute-ind-modality : ind-modality → UU (lsuc l1 ⊔ l2)
  compute-ind-modality ind-○ =
    (X : UU l1) (P : ○ X → UU l1) →
    (f : (x : X) → ○ (P (unit-○ x))) →
    (x : X) → ind-○ X P f (unit-○ x) ＝ f x

  dependent-universal-property-modality : UU (lsuc l1 ⊔ l2)
  dependent-universal-property-modality =
    Σ ind-modality compute-ind-modality

  rec-modality-ind-modality : ind-modality → rec-modality
  rec-modality-ind-modality ind X Y = ind X (λ _ → Y)
```

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
  ind-modality-is-higher-modality : is-higher-modality → ind-modality unit-○
  ind-modality-is-higher-modality = pr1 ∘ pr1

  rec-modality-is-higher-modality : is-higher-modality → rec-modality unit-○
  rec-modality-is-higher-modality =
    rec-modality-ind-modality unit-○ ∘ ind-modality-is-higher-modality

  compute-ind-modality-is-higher-modality :
    (h : is-higher-modality) →
    compute-ind-modality unit-○ (ind-modality-is-higher-modality h)
  compute-ind-modality-is-higher-modality = pr2 ∘ pr1

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

### Compoents of a higher modality

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

  ind-modality-higher-modality :
    ind-modality (unit-higher-modality)
  ind-modality-higher-modality =
    ind-modality-is-higher-modality
      ( locally-small-operator-higher-modality)
      ( unit-higher-modality)
      ( is-higher-modality-higher-modality)

  rec-modality-higher-modality :
    rec-modality (unit-higher-modality)
  rec-modality-higher-modality =
    rec-modality-ind-modality
      ( unit-higher-modality)
      ( ind-modality-higher-modality)

  compute-ind-modality-higher-modality :
    compute-ind-modality
      ( unit-higher-modality)
      ( ind-modality-higher-modality)
  compute-ind-modality-higher-modality =
    compute-ind-modality-is-higher-modality
      ( locally-small-operator-higher-modality)
      ( unit-higher-modality)
      ( is-higher-modality-higher-modality)

  is-modal-identity-types-higher-modality :
    is-modal-identity-types
      ( locally-small-operator-higher-modality)
      ( unit-higher-modality)
  is-modal-identity-types-higher-modality =
    ( is-modal-identity-types-is-higher-modality)
    ( locally-small-operator-higher-modality)
    ( unit-higher-modality)
    ( is-higher-modality-higher-modality)
```

## Properties

### The modal operator's action on maps

```agda
module _
  {l : Level}
  {○ : operator-modality l l} (unit-○ : unit-modality ○)
  where

  map-rec-modality :
    (rec-○ : rec-modality unit-○) {X Y : UU l} → (X → Y) → ○ X → ○ Y
  map-rec-modality rec-○ {X} {Y} f = rec-○ X Y (unit-○ ∘ f)
```

### Modal identity elimination

```agda
module _
  {l1 l2 : Level}
  ((○ , is-locally-small-○) : locally-small-operator-modality l1 l2 l1)
  (unit-○ : unit-modality ○)
  (Id-○ : is-modal-identity-types (○ , is-locally-small-○) unit-○)
  where

  elim-Id-higher-modality :
    {X : UU l1} {x' y' : ○ X} →
    ○ (type-is-small (is-locally-small-○ X x' y')) → x' ＝ y'
  elim-Id-higher-modality {X} {x'} {y'} =
    map-inv-unit-is-modal-type-is-small unit-○
      ( x' ＝ y')
      ( is-locally-small-○ X x' y')
      ( Id-○ X x' y')
```

### For homogenous higher modalities, The identity types of modal types are modal in the usual sense

```agda
module _
  {l : Level}
  ( ((○ , is-locally-small-○) , unit-○ , (ind-○ , compute-ind-○) , Id-○) :
      higher-modality l l)
  where

  map-inv-unit-id-higher-modality :
    {X : UU l} {x' y' : ○ X} → ○ (x' ＝ y') → x' ＝ y'
  map-inv-unit-id-higher-modality {X} {x'} {y'} =
    map-inv-unit-is-modal-type-is-small unit-○
      ( x' ＝ y')
      ( is-locally-small-○ X x' y')
      ( Id-○ X x' y') ∘
      ( map-rec-modality unit-○
        ( rec-modality-ind-modality unit-○ ind-○)
        ( map-equiv-is-small ( is-locally-small-○ X x' y')))
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
    map-inv-unit-id-higher-modality
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
module _
  {l : Level}
  ( ((○ , is-locally-small-○) , unit-○ , (ind-○ , compute-ind-○) , Id-○) :
      higher-modality l l)
  where

  is-retraction-ind-modality :
    {X : UU l} {P : ○ X → UU l} → (precomp-Π unit-○ (○ ∘ P) ∘ ind-○ X P) ~ id
  is-retraction-ind-modality {X} {P} = eq-htpy ∘ compute-ind-○ X P

  is-section-ind-modality :
    {X : UU l} {P : ○ X → UU l} → (ind-○ X P ∘ precomp-Π unit-○ (○ ∘ P)) ~ id
  is-section-ind-modality {X} {P} s =
    eq-htpy
      ( map-inv-unit-id-higher-modality
        ( (○ , is-locally-small-○) , unit-○ , (ind-○ , compute-ind-○) , Id-○) ∘
        ( ind-○ X
          ( λ x' → (ind-○ X P ∘ precomp-Π (unit-○) (○ ∘ P)) s x' ＝ s x')
          ( unit-○ ∘ compute-ind-○ X P (s ∘ unit-○))))

  is-equiv-ind-modality : (X : UU l) (P : ○ X → UU l) → is-equiv (ind-○ X P)
  pr1 (pr1 (is-equiv-ind-modality X P)) = precomp-Π unit-○ (○ ∘ P)
  pr2 (pr1 (is-equiv-ind-modality X P)) = is-section-ind-modality
  pr1 (pr2 (is-equiv-ind-modality X P)) = precomp-Π unit-○ (○ ∘ P)
  pr2 (pr2 (is-equiv-ind-modality X P)) = is-retraction-ind-modality

  equiv-ind-modality :
    (X : UU l) (P : ○ X → UU l) →
    ((x : X) → ○ (P (unit-○ x))) ≃ ((x' : ○ X) → ○ (P x'))
  pr1 (equiv-ind-modality X P) = ind-○ X P
  pr2 (equiv-ind-modality X P) = is-equiv-ind-modality X P

  is-uniquely-eliminating-modality-higher-modality :
    is-uniquely-eliminating-modality unit-○
  is-uniquely-eliminating-modality-higher-modality X P =
    is-equiv-map-inv-is-equiv (is-equiv-ind-modality X P)
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
