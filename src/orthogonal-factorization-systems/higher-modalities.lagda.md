# Higher modalities

```agda
module orthogonal-factorization-systems.higher-modalities where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equational-reasoning
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.functions
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.sections
open import foundation.small-types
open import foundation.subuniverses
open import foundation.universe-levels

open import orthogonal-factorization-systems.modal-operators
open import orthogonal-factorization-systems.uniquely-eliminating-modalities
```

</details>

## Idea

A **higher modality** is a _higher mode of logic_ defined in terms of a monadic
modal operator `○` satisfying a certain induction principle.

The induction principle states that for every type `X` and family `P : ○ X → UU`,
to define a dependent map `(x' : ○ X) → ○ (P x')` it suffices to define it on
the image of the modal unit, i.e. `(x : X) → ○ (P (unit-○ x))`. Moreover, it
satisfies a computation principle stating that when evaluating a map defined in
this manner on the image of the modal unit, one recovers the defining map
(propositionally).

Lastly, higher modalities must also be **identity closed** in the sense that
for every type `X` the identity types `(x' ＝ y')` are modal for all terms
`x' y' : ○ X`. Because of this, higher modalities in their most general form
only make sense for locally small modal operators.

## Definition

### The universal property of higher modalities

```agda
module _
  {l1 l2 : Level}
  {○ : modal-operator l1 l2}
  (unit-○ : modal-unit ○)
  where

  modal-ind : UU (lsuc l1 ⊔ l2)
  modal-ind =
    (X : UU l1) (P : ○ X → UU l1) →
    ((x : X) → ○ (P (unit-○ x))) →
    (x' : ○ X) → ○ (P x')

  modal-rec : UU (lsuc l1 ⊔ l2)
  modal-rec = (X Y : UU l1) → (X → ○ Y) → ○ X → ○ Y

  modal-comp : modal-ind → UU (lsuc l1 ⊔ l2)
  modal-comp ind-○ =
    (X : UU l1) (P : ○ X → UU l1) →
    (f : (x : X) → ○ (P (unit-○ x))) →
    (x : X) → ind-○ X P f (unit-○ x) ＝ f x

  modal-universal-property : UU (lsuc l1 ⊔ l2)
  modal-universal-property =
    Σ modal-ind modal-comp

  modal-rec-modal-ind : modal-ind → modal-rec
  modal-rec-modal-ind ind X Y = ind X (λ _ → Y)
```

### Closure under identity type formers

We say that the identity types of a locally small type are modal if their
small equivalent is modal.
We say that a modality is closed under identity type formation if for every
modal type, their identity types are also modal.

```agda
module _
  {l1 l2 : Level}
  ((○ , is-locally-small-○) : locally-small-modal-operator l1 l2 l1)
  (unit-○ : modal-unit ○)
  where

  is-modal-identity-types : UU (lsuc l1 ⊔ l2)
  is-modal-identity-types =
    (X : UU l1) (x y : ○ X) →
    is-modal (unit-○) (type-is-small (is-locally-small-○ X x y))
```

### The `is-higher-modality` predicate

```agda
  is-higher-modality : UU (lsuc l1 ⊔ l2)
  is-higher-modality =
    modal-universal-property (unit-○) × is-modal-identity-types
```

### Projections for the `is-higher-modality` predicate

```agda
  modal-ind-is-higher-modality : is-higher-modality → modal-ind unit-○
  modal-ind-is-higher-modality = pr1 ∘ pr1

  modal-rec-is-higher-modality : is-higher-modality → modal-rec unit-○
  modal-rec-is-higher-modality =
    modal-rec-modal-ind unit-○ ∘ modal-ind-is-higher-modality

  modal-comp-is-higher-modality :
    (h : is-higher-modality) →
    modal-comp unit-○ (modal-ind-is-higher-modality h)
  modal-comp-is-higher-modality = pr2 ∘ pr1

  is-modal-identity-types-is-higher-modality :
    is-higher-modality → is-modal-identity-types
  is-modal-identity-types-is-higher-modality = pr2
```

### The structure of a higher modality

```agda
higher-modality : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
higher-modality l1 l2 =
  Σ ( locally-small-modal-operator l1 l2 l1)
    ( λ ○ →
      Σ ( modal-unit (pr1 ○))
        ( is-higher-modality ○))
```

### Projections for `higher-modality`

```agda
module _
  {l1 l2 : Level} (h : higher-modality l1 l2)
    where

  locally-small-modal-operator-higher-modality :
    locally-small-modal-operator l1 l2 l1
  locally-small-modal-operator-higher-modality = pr1 h

  modal-operator-higher-modality : modal-operator l1 l2
  modal-operator-higher-modality =
    modal-operator-locally-small-modal-operator
      ( locally-small-modal-operator-higher-modality)

  is-locally-small-modal-operator-higher-modality :
    is-locally-small-modal-operator (modal-operator-higher-modality)
  is-locally-small-modal-operator-higher-modality =
    is-locally-small-locally-small-modal-operator
      ( locally-small-modal-operator-higher-modality)

  modal-unit-higher-modality :
    modal-unit (modal-operator-higher-modality)
  modal-unit-higher-modality = pr1 (pr2 h)

  is-higher-modality-higher-modality :
    is-higher-modality
      ( locally-small-modal-operator-higher-modality)
      ( modal-unit-higher-modality)
  is-higher-modality-higher-modality = pr2 (pr2 h)

  modal-ind-higher-modality :
    modal-ind (modal-unit-higher-modality)
  modal-ind-higher-modality =
    modal-ind-is-higher-modality
      ( locally-small-modal-operator-higher-modality)
      ( modal-unit-higher-modality)
      ( is-higher-modality-higher-modality)

  modal-rec-higher-modality :
    modal-rec (modal-unit-higher-modality)
  modal-rec-higher-modality =
    modal-rec-modal-ind
      ( modal-unit-higher-modality)
      ( modal-ind-higher-modality)

  modal-comp-higher-modality :
    modal-comp
      ( modal-unit-higher-modality)
      ( modal-ind-higher-modality)
  modal-comp-higher-modality =
    modal-comp-is-higher-modality
      ( locally-small-modal-operator-higher-modality)
      ( modal-unit-higher-modality)
      ( is-higher-modality-higher-modality)

  is-modal-identity-types-higher-modality :
    is-modal-identity-types
      ( locally-small-modal-operator-higher-modality)
      ( modal-unit-higher-modality)
  is-modal-identity-types-higher-modality =
    ( is-modal-identity-types-is-higher-modality)
    ( locally-small-modal-operator-higher-modality)
    ( modal-unit-higher-modality)
    ( is-higher-modality-higher-modality)
```

## Properties

### The modal operator's action on maps

```agda
module _
  {l : Level}
  {○ : modal-operator l l} (unit-○ : modal-unit ○)
  where

  map-modal-rec : (rec-○ : modal-rec unit-○) {X Y : UU l} → (X → Y) → ○ X → ○ Y
  map-modal-rec rec-○ {X} {Y} f = rec-○ X Y (unit-○ ∘ f)
```

### Modal identity elimination

```agda
module _
  {l1 l2 : Level}
  ((○ , is-locally-small-○) : locally-small-modal-operator l1 l2 l1)
  (unit-○ : modal-unit ○)
  (Id-○ : is-modal-identity-types (○ , is-locally-small-○) unit-○)
  where

  id-elim-higher-modality :
    {X : UU l1} {x' y' : ○ X} →
    ○ (type-is-small (is-locally-small-○ X x' y')) → x' ＝ y'
  id-elim-higher-modality {X} {x'} {y'} =
    map-inv-unit-is-modal-is-small unit-○
      ( x' ＝ y')
      ( is-locally-small-○ X x' y')
      ( Id-○ X x' y')
```

Homogenous higher modalities are closed under identity formation in the usual sense

```agda
module _
  {l : Level}
  (((○ , is-locally-small-○) , unit-○ , (ind-○ , comp-○) , Id-○) : higher-modality l l)
  where

  map-inv-unit-id-higher-modality :
    {X : UU l} {x' y' : ○ X} → ○ (x' ＝ y') → x' ＝ y'
  map-inv-unit-id-higher-modality {X} {x'} {y'} =
    map-inv-unit-is-modal-is-small unit-○
      ( x' ＝ y')
      ( is-locally-small-○ X x' y')
      ( Id-○ X x' y') ∘
      ( map-modal-rec unit-○
        ( modal-rec-modal-ind unit-○ ind-○)
        ( map-equiv-is-small ( is-locally-small-○ X x' y')))
```

### `○ X` is modal

```agda
module _
  {l : Level}
  (((○ , is-locally-small-○) , unit-○ , (ind-○ , comp-○) , Id-○) : higher-modality l l)
  (X : UU l)
  where

  map-inv-modal-unit : ○ (○ X) → ○ X
  map-inv-modal-unit = ind-○ (○ X) (λ _ → X) id

  isretr-map-inv-modal-unit : (map-inv-modal-unit ∘ unit-○) ~ id
  isretr-map-inv-modal-unit = comp-○ (○ X) (λ _ → X) id

  issec-map-inv-modal-unit : (unit-○ ∘ map-inv-modal-unit) ~ id
  issec-map-inv-modal-unit x'' =
    map-inv-unit-id-higher-modality
      ( (○ , is-locally-small-○) , unit-○ , (ind-○ , comp-○) , Id-○)
      ( ind-○ (○ X)
        ( λ x'' → unit-○ (map-inv-modal-unit x'') ＝ x'')
        ( unit-○ ∘ (ap unit-○ ∘ isretr-map-inv-modal-unit)) x'')

  is-modal-modal-operator-type : is-modal unit-○ (○ X)
  pr1 (pr1 is-modal-modal-operator-type) = map-inv-modal-unit
  pr2 (pr1 is-modal-modal-operator-type) = issec-map-inv-modal-unit
  pr1 (pr2 is-modal-modal-operator-type) = map-inv-modal-unit
  pr2 (pr2 is-modal-modal-operator-type) = isretr-map-inv-modal-unit
```

## Higher modalities are uniquely eliminating modalities

```agda
module _
  {l : Level}
  (((○ , is-locally-small-○) , unit-○ , (ind-○ , comp-○) , Id-○) : higher-modality l l)
  where

  isretr-modal-ind :
    {X : UU l} {P : ○ X → UU l} → (precomp-Π unit-○ (○ ∘ P) ∘ ind-○ X P) ~ id
  isretr-modal-ind {X} {P} = eq-htpy ∘ comp-○ X P

  issec-modal-ind :
    {X : UU l} {P : ○ X → UU l} → (ind-○ X P ∘ precomp-Π unit-○ (○ ∘ P)) ~ id
  issec-modal-ind {X} {P} s =
    eq-htpy
      ( map-inv-unit-id-higher-modality
        ( (○ , is-locally-small-○) , unit-○ , (ind-○ , comp-○) , Id-○) ∘
        ( ind-○ X
          ( λ x' → (ind-○ X P ∘ precomp-Π (unit-○) (○ ∘ P)) s x' ＝ s x')
          ( unit-○ ∘ comp-○ X P (s ∘ unit-○))))

  is-equiv-modal-ind : (X : UU l) (P : ○ X → UU l) → is-equiv (ind-○ X P)
  pr1 (pr1 (is-equiv-modal-ind X P)) = precomp-Π unit-○ (○ ∘ P)
  pr2 (pr1 (is-equiv-modal-ind X P)) = issec-modal-ind
  pr1 (pr2 (is-equiv-modal-ind X P)) = precomp-Π unit-○ (○ ∘ P)
  pr2 (pr2 (is-equiv-modal-ind X P)) = isretr-modal-ind

  equiv-modal-ind :
    (X : UU l) (P : ○ X → UU l) →
    ((x : X) → ○ (P (unit-○ x))) ≃ ((x' : ○ X) → ○ (P x'))
  pr1 (equiv-modal-ind X P) = ind-○ X P
  pr2 (equiv-modal-ind X P) = is-equiv-modal-ind X P

  is-uniquely-eliminating-modality-higher-modality :
    is-uniquely-eliminating-modality unit-○
  is-uniquely-eliminating-modality-higher-modality X P =
    is-equiv-map-inv-is-equiv (is-equiv-modal-ind X P)
```

## See also

The equivalent notions of
- [Uniquely eliminating modalities](orthogonal-factorization-systems.uniquely-eliminating-modalities.md)
- [Σ-closed reflective subuniverses](orthogonal-factorization-systems.reflective-subuniverses.md)
- [Orthogonal factorization systems](orthogonal-factorization-systems.orthogonal-factorization-systems.md)

## References

- Egbert Rijke, Michael Shulman, Bas Spitters, _Modalities in homotopy type theory_, Logical Methods in Computer Science, Volume 16, Issue 1, 2020 ([arXiv:1706.07526](https://arxiv.org/abs/1706.07526), [doi:10.23638](https://doi.org/10.23638/LMCS-16%281%3A2%292020))
