# Suspensions of propositions

```agda
module synthetic-homotopy-theory.suspensions-of-propositions where
```

<details><summary>Imports</summary>

```agda
open import foundation.booleans
open import foundation.contractible-types
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.set-truncations
open import foundation.propositional-truncations
open import foundation.subsingleton-induction
open import foundation.surjective-maps
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.univalence
open import foundation.universe-levels

open import synthetic-homotopy-theory.dependent-suspension-structures
open import synthetic-homotopy-theory.suspension-structures
open import synthetic-homotopy-theory.suspensions-of-types

open import univalent-combinatorics.kuratowski-finite-sets
```

</details>

## Idea

The
{{#concept "suspension" Disambiguation="of a proposition" Agda=suspension-Prop}}
of a [proposition](foundation-core.propositions.md) `P` is the
[set](foundation.sets.md) satisfying the
[universal property of the pushout](synthetic-homotopy-theory.universal-property-pushouts.md)
of the [span](foundation.spans.md)

```text
  1 <--- P ---> 1.
```

## Definitions

### The suspension of a proposition

```agda
module _
  {l : Level} (P : Prop l)
  where

  suspension-Prop : UU l
  suspension-Prop = suspension (type-Prop P)
```

### Suspensions of propositions are sets

We characterize equality in the suspension of a proposition `P` by the following
four equations

```text
  (N ＝ N) ≃ 1
  (N ＝ S) ≃ P
  (S ＝ N) ≃ P
  (S ＝ S) ≃ 1.
```

Since these are all propositions, `ΣP` forms a set. This is Lemma 10.1.13 in
{{#cite UF13}}.

First we define the observational equality family on `ΣP`.

```agda
module _
  {l : Level} (P : Prop l)
  where

  suspension-structure-Eq-north-suspension-Prop :
    suspension-structure (type-Prop P) (UU l)
  suspension-structure-Eq-north-suspension-Prop =
    ( raise-unit l) ,
    ( type-Prop P) ,
    ( λ x →
      inv
        ( eq-equiv
          ( equiv-raise-unit-is-contr (is-proof-irrelevant-type-Prop P x))))

  Eq-north-suspension-Prop :
    suspension (type-Prop P) → UU l
  Eq-north-suspension-Prop =
    cogap-suspension suspension-structure-Eq-north-suspension-Prop

  suspension-structure-Eq-south-suspension-Prop :
    suspension-structure (type-Prop P) (UU l)
  suspension-structure-Eq-south-suspension-Prop =
    ( type-Prop P) ,
    ( raise-unit l) ,
    ( λ x →
      eq-equiv (equiv-raise-unit-is-contr (is-proof-irrelevant-type-Prop P x)))

  Eq-south-suspension-Prop :
    suspension (type-Prop P) → UU l
  Eq-south-suspension-Prop =
    cogap-suspension suspension-structure-Eq-south-suspension-Prop

  abstract
    coh-Eq-suspension-Prop :
      type-Prop P → Eq-north-suspension-Prop ~ Eq-south-suspension-Prop
    coh-Eq-suspension-Prop x =
      dependent-cogap-suspension
        ( eq-value
          ( Eq-north-suspension-Prop)
          ( Eq-south-suspension-Prop))
        ( ( ( compute-north-cogap-suspension
              ( suspension-structure-Eq-north-suspension-Prop)) ∙
            ( inv
              ( eq-equiv
                ( equiv-raise-unit-is-contr
                  ( is-proof-irrelevant-type-Prop P x)))) ∙
            ( inv
              ( compute-north-cogap-suspension
                ( suspension-structure-Eq-south-suspension-Prop)))) ,
          ( ( compute-south-cogap-suspension
              ( suspension-structure-Eq-north-suspension-Prop)) ∙
            ( eq-equiv
              ( equiv-raise-unit-is-contr
                ( is-proof-irrelevant-type-Prop P x))) ∙
            ( inv
              ( compute-south-cogap-suspension
                ( suspension-structure-Eq-south-suspension-Prop)))) ,
          ind-subsingleton
            ( is-prop-type-Prop P)
            ( x)
            ( eq-is-contr
              ( is-contr-equiv
                ( type-Prop P ≃ raise-unit l)
                ( equiv-univalence ∘e
                  equiv-binary-concat
                    ( inv
                      ( compute-south-cogap-suspension
                        ( suspension-structure-Eq-north-suspension-Prop)))
                    ( compute-south-cogap-suspension
                      ( suspension-structure-Eq-south-suspension-Prop)))
                ( is-contr-equiv-is-contr
                  ( is-proof-irrelevant-type-Prop P x)
                  ( is-contr-raise-unit)))))

  suspension-structure-Eq-suspension-Prop :
    suspension-structure (type-Prop P) (suspension-Prop P → UU l)
  suspension-structure-Eq-suspension-Prop =
      ( Eq-north-suspension-Prop ,
        Eq-south-suspension-Prop ,
        eq-htpy ∘ coh-Eq-suspension-Prop)

  Eq-suspension-Prop :
    suspension-Prop P → suspension-Prop P → UU l
  Eq-suspension-Prop =
    cogap-suspension suspension-structure-Eq-suspension-Prop
```

We compute the observational equality of the suspension of a proposition at the
poles.

```agda
  eq-compute-Eq-north-north-suspension-Prop :
    Eq-suspension-Prop north-suspension north-suspension ＝ raise-unit l
  eq-compute-Eq-north-north-suspension-Prop =
    htpy-eq
      ( compute-north-cogap-suspension suspension-structure-Eq-suspension-Prop)
      ( north-suspension) ∙
    compute-north-cogap-suspension suspension-structure-Eq-north-suspension-Prop

  compute-Eq-north-north-suspension-Prop :
    Eq-suspension-Prop north-suspension north-suspension ≃ unit
  compute-Eq-north-north-suspension-Prop =
    inv-compute-raise-unit l ∘e
    equiv-eq eq-compute-Eq-north-north-suspension-Prop

  is-contr-Eq-north-north-suspension-Prop :
    is-contr (Eq-suspension-Prop north-suspension north-suspension)
  is-contr-Eq-north-north-suspension-Prop =
    is-contr-equiv-raise-unit
      ( equiv-eq eq-compute-Eq-north-north-suspension-Prop)

  eq-compute-Eq-south-south-suspension-Prop :
    Eq-suspension-Prop south-suspension south-suspension ＝ raise-unit l
  eq-compute-Eq-south-south-suspension-Prop =
    htpy-eq
      ( compute-south-cogap-suspension suspension-structure-Eq-suspension-Prop)
      ( south-suspension) ∙
    compute-south-cogap-suspension suspension-structure-Eq-south-suspension-Prop

  compute-Eq-south-south-suspension-Prop :
    Eq-suspension-Prop south-suspension south-suspension ≃ unit
  compute-Eq-south-south-suspension-Prop =
    inv-compute-raise-unit l ∘e
    equiv-eq eq-compute-Eq-south-south-suspension-Prop

  is-contr-Eq-south-south-suspension-Prop :
    is-contr (Eq-suspension-Prop south-suspension south-suspension)
  is-contr-Eq-south-south-suspension-Prop =
    is-contr-equiv-raise-unit
      ( equiv-eq eq-compute-Eq-south-south-suspension-Prop)

  eq-compute-Eq-north-south-suspension-Prop :
    Eq-suspension-Prop north-suspension south-suspension ＝ type-Prop P
  eq-compute-Eq-north-south-suspension-Prop =
    htpy-eq
      ( compute-north-cogap-suspension suspension-structure-Eq-suspension-Prop)
      ( south-suspension) ∙
    compute-south-cogap-suspension suspension-structure-Eq-north-suspension-Prop

  eq-compute-Eq-south-north-suspension-Prop :
    Eq-suspension-Prop south-suspension north-suspension ＝ type-Prop P
  eq-compute-Eq-south-north-suspension-Prop =
    htpy-eq
      ( compute-south-cogap-suspension suspension-structure-Eq-suspension-Prop)
      ( north-suspension) ∙
    compute-north-cogap-suspension suspension-structure-Eq-south-suspension-Prop
```

The observational equality on the suspension of a proposition is propositional.

```agda
  abstract
    is-prop-Eq-north-suspension-Prop :
      (y : suspension-Prop P) → is-prop (Eq-north-suspension-Prop y)
    is-prop-Eq-north-suspension-Prop =
      dependent-cogap-suspension
        ( λ x → is-prop (Eq-north-suspension-Prop x))
        ( ( inv-tr
            ( is-prop)
            ( compute-north-cogap-suspension
              ( suspension-structure-Eq-north-suspension-Prop))
            ( is-prop-raise-unit)) ,
          ( inv-tr
            ( is-prop)
            ( compute-south-cogap-suspension
              ( suspension-structure-Eq-north-suspension-Prop))
            ( is-prop-type-Prop P)) ,
          ( λ _ →
            eq-is-prop
              ( is-prop-is-prop (Eq-north-suspension-Prop south-suspension))))

  abstract
    is-prop-Eq-south-suspension-Prop :
      (y : suspension-Prop P) → is-prop (Eq-south-suspension-Prop y)
    is-prop-Eq-south-suspension-Prop =
      dependent-cogap-suspension
        ( λ x → is-prop (Eq-south-suspension-Prop x))
        ( ( inv-tr
            ( is-prop)
            ( compute-north-cogap-suspension
              ( suspension-structure-Eq-south-suspension-Prop))
            ( is-prop-type-Prop P)) ,
          ( inv-tr
            ( is-prop)
            ( compute-south-cogap-suspension
              ( suspension-structure-Eq-south-suspension-Prop))
            ( is-prop-raise-unit)) ,
          ( λ _ →
            eq-is-prop
              ( is-prop-is-prop (Eq-south-suspension-Prop south-suspension))))

  abstract
    is-prop-Eq-suspension-Prop :
      (x y : suspension-Prop P) → is-prop (Eq-suspension-Prop x y)
    is-prop-Eq-suspension-Prop x y =
      dependent-cogap-suspension
        ( λ x → is-prop (Eq-suspension-Prop x y))
        ( ( inv-tr
            ( is-prop)
            ( htpy-eq
              ( compute-north-cogap-suspension
                ( suspension-structure-Eq-suspension-Prop))
              ( y))
            ( is-prop-Eq-north-suspension-Prop y)) ,
          ( inv-tr
            ( is-prop)
            ( htpy-eq
              ( compute-south-cogap-suspension
                ( suspension-structure-Eq-suspension-Prop))
              ( y))
            ( is-prop-Eq-south-suspension-Prop y)) ,
          ( λ _ →
            eq-is-prop
              ( is-prop-is-prop (Eq-suspension-Prop south-suspension y))))
        ( x)
```

The observational equality characterizes equality in `ΣP`.

```agda
  refl-Eq-suspension-Prop : (x : suspension-Prop P) → Eq-suspension-Prop x x
  refl-Eq-suspension-Prop =
    dependent-cogap-suspension
      ( λ x → Eq-suspension-Prop x x)
      ( ( map-inv-eq
          ( ( htpy-eq
              ( compute-north-cogap-suspension
                ( suspension-structure-Eq-suspension-Prop))
              ( north-suspension)) ∙
            ( compute-north-cogap-suspension
              ( suspension-structure-Eq-north-suspension-Prop)))
          ( raise-star)) ,
        ( map-inv-eq
          ( ( htpy-eq
              ( compute-south-cogap-suspension
                ( suspension-structure-Eq-suspension-Prop))
              ( south-suspension)) ∙
            ( compute-south-cogap-suspension
              ( suspension-structure-Eq-south-suspension-Prop)))
          ( raise-star)) ,
        ( λ _ →
          eq-is-contr
            ( inv-tr
              ( is-contr)
              ( eq-compute-Eq-south-south-suspension-Prop)
              ( is-contr-raise-unit))))

  Eq-eq-suspension-Prop :
    (x y : suspension-Prop P) → x ＝ y → Eq-suspension-Prop x y
  Eq-eq-suspension-Prop x .x refl = refl-Eq-suspension-Prop x

  dependent-suspension-structure-eq-north-Eq-north-suspension-Prop :
    dependent-suspension-structure
      ( λ y → Eq-suspension-Prop north-suspension y → north-suspension ＝ y)
      ( suspension-structure-suspension (type-Prop P))
  dependent-suspension-structure-eq-north-Eq-north-suspension-Prop =
    ( ( λ _ → refl) ,
      ( λ u →
        meridian-suspension
          ( map-eq eq-compute-Eq-north-south-suspension-Prop u)) ,
      ( λ p →
        eq-is-contr
          ( is-contr-function-type
            ( is-prop-is-contr
              ( is-contr-suspension-is-contr
                ( is-proof-irrelevant-type-Prop P p))
              ( north-suspension)
              ( south-suspension)))))

  eq-north-Eq-north-suspension-Prop :
    (y : suspension-Prop P) →
    Eq-suspension-Prop north-suspension y → north-suspension ＝ y
  eq-north-Eq-north-suspension-Prop =
    dependent-cogap-suspension
      ( λ y → Eq-suspension-Prop north-suspension y → north-suspension ＝ y)
      ( dependent-suspension-structure-eq-north-Eq-north-suspension-Prop)

  dependent-suspension-structure-eq-south-Eq-south-suspension-Prop :
    dependent-suspension-structure
      ( λ y → Eq-suspension-Prop south-suspension y → south-suspension ＝ y)
      ( suspension-structure-suspension (type-Prop P))
  dependent-suspension-structure-eq-south-Eq-south-suspension-Prop =
    ( ( λ u →
        inv
          ( meridian-suspension
            ( map-eq eq-compute-Eq-south-north-suspension-Prop u))) ,
      ( λ _ → refl) ,
      ( λ p →
        eq-is-contr
          ( is-contr-function-type
            ( is-prop-is-contr
              ( is-contr-suspension-is-contr
                ( is-proof-irrelevant-type-Prop P p))
              ( south-suspension)
              ( south-suspension)))))

  eq-south-Eq-south-suspension-Prop :
    (y : suspension-Prop P) →
    Eq-suspension-Prop south-suspension y → south-suspension ＝ y
  eq-south-Eq-south-suspension-Prop =
    dependent-cogap-suspension
      ( λ y → Eq-suspension-Prop south-suspension y → south-suspension ＝ y)
      ( dependent-suspension-structure-eq-south-Eq-south-suspension-Prop)

  eq-Eq-suspension-Prop :
    (x y : suspension-Prop P) → Eq-suspension-Prop x y → x ＝ y
  eq-Eq-suspension-Prop =
    dependent-cogap-suspension
      ( λ x → (y : suspension-Prop P) → Eq-suspension-Prop x y → x ＝ y)
      ( ( eq-north-Eq-north-suspension-Prop) ,
        ( eq-south-Eq-south-suspension-Prop) ,
        ( λ p →
          eq-is-contr
            ( is-contr-Π
              ( λ y →
                is-contr-function-type
                  ( is-prop-is-contr
                    ( is-contr-suspension-is-contr
                      ( is-proof-irrelevant-type-Prop P p))
                    ( south-suspension)
                    ( y))))))

  abstract
    is-equiv-Eq-eq-suspension-Prop :
      (x y : suspension-Prop P) → is-equiv (Eq-eq-suspension-Prop x y)
    is-equiv-Eq-eq-suspension-Prop x =
      fundamental-theorem-id-section
        ( x)
        ( Eq-eq-suspension-Prop x)
        ( λ y →
          ( eq-Eq-suspension-Prop x y) ,
          ( λ _ → eq-is-prop (is-prop-Eq-suspension-Prop x y)))

  abstract
    is-equiv-eq-Eq-suspension-Prop :
      (x y : suspension-Prop P) → is-equiv (eq-Eq-suspension-Prop x y)
    is-equiv-eq-Eq-suspension-Prop x =
      fundamental-theorem-id-retraction
        ( x)
        ( eq-Eq-suspension-Prop x)
        ( λ y →
          ( Eq-eq-suspension-Prop x y) ,
          ( λ _ → eq-is-prop (is-prop-Eq-suspension-Prop x y)))

  equiv-Eq-eq-suspension-Prop :
    (x y : suspension-Prop P) → (x ＝ y) ≃ Eq-suspension-Prop x y
  equiv-Eq-eq-suspension-Prop x y =
    ( Eq-eq-suspension-Prop x y , is-equiv-Eq-eq-suspension-Prop x y)

  equiv-eq-Eq-suspension-Prop :
    (x y : suspension-Prop P) → Eq-suspension-Prop x y ≃ (x ＝ y)
  equiv-eq-Eq-suspension-Prop x y =
    ( eq-Eq-suspension-Prop x y , is-equiv-eq-Eq-suspension-Prop x y)

  abstract
    is-torsorial-Eq-suspension-Prop :
      (x : suspension-Prop P) → is-torsorial (Eq-suspension-Prop x)
    is-torsorial-Eq-suspension-Prop x =
      fundamental-theorem-id'
        ( Eq-eq-suspension-Prop x)
        ( is-equiv-Eq-eq-suspension-Prop x)
```

Piecing it all together, we conclude that suspensions of propositions are sets.

```agda
  abstract
    is-set-suspension-Prop : is-set (suspension-Prop P)
    is-set-suspension-Prop x y =
      is-prop-equiv
        ( equiv-Eq-eq-suspension-Prop x y)
        ( is-prop-Eq-suspension-Prop x y)

  suspension-set-Prop : Set l
  suspension-set-Prop = suspension-Prop P , is-set-suspension-Prop
```

```agda
  compute-eq-north-south-suspension-Prop :
    (north-suspension {X = type-Prop P} ＝ south-suspension) ≃ type-Prop P
  compute-eq-north-south-suspension-Prop =
    equiv-eq eq-compute-Eq-north-south-suspension-Prop ∘e
    equiv-Eq-eq-suspension-Prop north-suspension south-suspension

  compute-eq-south-north-suspension-Prop :
    (south-suspension {X = type-Prop P} ＝ north-suspension) ≃ type-Prop P
  compute-eq-south-north-suspension-Prop =
    equiv-eq eq-compute-Eq-south-north-suspension-Prop ∘e
    equiv-Eq-eq-suspension-Prop south-suspension north-suspension
```

### Suspensions of propositions are Kuratowski finite sets

```agda
module _
  {l : Level} (P : Prop l)
  where

  is-kuratowski-finite-set-suspension-set-Prop :
    is-kuratowski-finite-Set (suspension-set-Prop P)
  is-kuratowski-finite-set-suspension-set-Prop =
    intro-exists 2
      ( comp-surjection
        ( surjection-bool-suspension)
        ( surjection-equiv equiv-bool-Fin-2))
```

### Suspensions _almost_ commute with propositional truncations

The problem is that empty types suspend to a two-element set. This is easily
fixed by adjusting the truncation level, and we do have that
`Σ (trunc-Prop X) = trunc-Set (Σ X)`.

```agda
module _
  {l : Level} (X : UU l)
  where

  suspension-structure-suspension-trunc-prop-trunc-set-suspension :
    suspension-structure (type-trunc-Prop X) (type-trunc-Set (suspension X))
  pr1 suspension-structure-suspension-trunc-prop-trunc-set-suspension =
    unit-trunc-Set north-suspension
  pr1 (pr2 suspension-structure-suspension-trunc-prop-trunc-set-suspension) =
    unit-trunc-Set south-suspension
  pr2 (pr2 suspension-structure-suspension-trunc-prop-trunc-set-suspension) =
    rec-trunc-Prop
      ( Id-Prop
        ( trunc-Set (suspension X))
        ( unit-trunc-Set north-suspension)
        ( unit-trunc-Set south-suspension))
      ( λ x → ap unit-trunc-Set (meridian-suspension x))

  suspension-trunc-prop-trunc-set-suspension :
    suspension (type-trunc-Prop X) → type-trunc-Set (suspension X)
  suspension-trunc-prop-trunc-set-suspension =
    cogap-suspension
      ( suspension-structure-suspension-trunc-prop-trunc-set-suspension)

  suspension-structure-trunc-set-suspension-suspension-trunc-prop :
    suspension-structure X (suspension (type-trunc-Prop X))
  pr1 suspension-structure-trunc-set-suspension-suspension-trunc-prop =
    north-suspension
  pr1 (pr2 suspension-structure-trunc-set-suspension-suspension-trunc-prop) =
    south-suspension
  pr2 (pr2 suspension-structure-trunc-set-suspension-suspension-trunc-prop) x =
    meridian-suspension (unit-trunc-Prop x)

  trunc-set-suspension-suspension-trunc-prop :
    type-trunc-Set (suspension X) → suspension (type-trunc-Prop X)
  trunc-set-suspension-suspension-trunc-prop =
    map-universal-property-trunc-Set
      ( suspension-set-Prop (trunc-Prop X))
      ( cogap-suspension
          suspension-structure-trunc-set-suspension-suspension-trunc-prop)

  dependent-suspension-structure-retraction-suspension-trunc-prop-trunc-set-suspension :
    dependent-suspension-structure
      ( λ z →
        ( trunc-set-suspension-suspension-trunc-prop ∘
          suspension-trunc-prop-trunc-set-suspension)
        ( z)
        ＝ z)
      ( suspension-structure-suspension (type-trunc-Prop X))
  pr1 dependent-suspension-structure-retraction-suspension-trunc-prop-trunc-set-suspension =
    ap trunc-set-suspension-suspension-trunc-prop {!   !} ∙ {!   !}
  pr1 (pr2 dependent-suspension-structure-retraction-suspension-trunc-prop-trunc-set-suspension) =
    ap trunc-set-suspension-suspension-trunc-prop {!   !} ∙ {!   !}
  pr2 (pr2 dependent-suspension-structure-retraction-suspension-trunc-prop-trunc-set-suspension) x =
    eq-is-prop {! is-set  !}

  suspension-structure-eq-trunc-set-suspension :
    (x : type-trunc-Set (suspension X)) →
    suspension-structure
      (X)
      ((suspension-trunc-prop-trunc-set-suspension ∘
        trunc-set-suspension-suspension-trunc-prop)
        x ＝
      x)
  pr1 (suspension-structure-eq-trunc-set-suspension x) = {!   !}
  pr1 (pr2 (suspension-structure-eq-trunc-set-suspension x)) = {!   !}
  pr2 (pr2 (suspension-structure-eq-trunc-set-suspension x)) = {!   !}

  is-equiv-suspension-trunc-prop-trunc-set-suspension :
    is-equiv suspension-trunc-prop-trunc-set-suspension
  pr1 (pr1 is-equiv-suspension-trunc-prop-trunc-set-suspension) =
    trunc-set-suspension-suspension-trunc-prop
  pr2 (pr1 is-equiv-suspension-trunc-prop-trunc-set-suspension) x =
    apply-universal-property-trunc-Set
      ( set-Prop
        ( Id-Prop
          ( trunc-Set (suspension X))
          ( ( suspension-trunc-prop-trunc-set-suspension ∘
              trunc-set-suspension-suspension-trunc-prop)
            x)
          ( x)))
        ( x)
        ( cogap-suspension (suspension-structure-eq-trunc-set-suspension x))
  pr1 (pr2 is-equiv-suspension-trunc-prop-trunc-set-suspension) =
    trunc-set-suspension-suspension-trunc-prop
  pr2 (pr2 is-equiv-suspension-trunc-prop-trunc-set-suspension) =
    dependent-cogap-suspension
      ( λ z →
        ( trunc-set-suspension-suspension-trunc-prop ∘
          suspension-trunc-prop-trunc-set-suspension)
        ( z)
        ＝ z)
      ( dependent-suspension-structure-retraction-suspension-trunc-prop-trunc-set-suspension)
```

## See also

- Suspensions of propositions are used in the proof of
  [Diaconescu's theorem](foundation.diaconescus-theorem.md), which states that
  the axiom of choice implies the law of excluded middle.

## References

{{#bibliography}}

## External links

- [Truncatedness, properties of suspensions](https://1lab.dev/Homotopy.Space.Suspension.Properties.html#truncatedness)
  at 1lab
