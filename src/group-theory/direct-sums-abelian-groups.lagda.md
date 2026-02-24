# Direct sums of Abelian groups

```agda
module group-theory.direct-sums-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.decidable-equality
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.full-subtypes
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-disjunction
open import foundation.functoriality-propositional-truncation
open import foundation.identity-types
open import foundation.negated-equality
open import foundation.propositions
open import foundation.sets
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.dependent-products-abelian-groups
open import group-theory.full-subgroups
open import group-theory.homomorphisms-abelian-groups
open import group-theory.isomorphisms-abelian-groups
open import group-theory.subgroups-abelian-groups
open import group-theory.subsets-abelian-groups

open import univalent-combinatorics.finitely-enumerable-subtypes
open import univalent-combinatorics.finitely-enumerable-types
```

</details>

## Idea

The
{{#concept "direct sum" WDID=Q13582243 WD="direct sum" Disambiguation="of a family of abelian groups" Agda=∑-Ab}}
of a family of [abelian groups](group-theory.abelian-groups.md) `Gᵢ` indexed by
a type `I` is the [subgroup](group-theory.subgroups-abelian-groups.md) of the
[dependent product](group-theory.dependent-products-abelian-groups.md) of the
`Gᵢ` containing those elements `f : I → Gᵢ` such that `f` is zero except on a
[finitely enumerable subtype](univalent-combinatorics.finitely-enumerable-subtypes.md)
of `I`.

## Definition

```agda
module _
  {l1 l2 : Level}
  (I : UU l1)
  (G : I → Ab l2)
  where

  has-finite-support-prop-type-Π-Ab :
    type-Π-Ab I G → Prop (lsuc l1 ⊔ l2)
  has-finite-support-prop-type-Π-Ab f =
    ∃ ( finitely-enumerable-subtype l1 I)
      ( λ F →
        Π-Prop
          ( I)
          ( λ i →
            ( subtype-finitely-enumerable-subtype F i) ∨
            ( is-zero-prop-Ab (G i) (f i))))

  has-finite-support-type-Π-Ab :
    type-Π-Ab I G → UU (lsuc l1 ⊔ l2)
  has-finite-support-type-Π-Ab f =
    type-Prop (has-finite-support-prop-type-Π-Ab f)

  abstract
    has-finite-support-zero-Π-Ab :
      has-finite-support-type-Π-Ab (zero-Π-Ab I G)
    has-finite-support-zero-Π-Ab =
      intro-exists
        ( empty-finitely-enumerable-subtype l1 I)
        ( λ i → inr-disjunction refl)

    is-closed-under-addition-has-finite-support-type-Π-Ab :
      is-closed-under-addition-subset-Ab
        ( Π-Ab I G)
        ( has-finite-support-prop-type-Π-Ab)
    is-closed-under-addition-has-finite-support-type-Π-Ab
      {f} {g} =
      map-binary-trunc-Prop
        ( λ (Ff , Hf) (Fg , Hg) →
          ( union-finitely-enumerable-subtype Ff Fg ,
            λ i →
              let
                motive =
                  ( subtype-union-finitely-enumerable-subtype Ff Fg i) ∨
                  ( is-zero-prop-Ab (G i) (add-Π-Ab I G f g i))
              in
                elim-disjunction
                  ( motive)
                  ( inl-disjunction ∘ inl-disjunction)
                  ( λ fi=0 →
                    elim-disjunction
                      ( motive)
                      ( inl-disjunction ∘ inr-disjunction)
                      ( λ gi=0 →
                        inr-disjunction
                          ( ( ap-add-Ab (G i) fi=0 gi=0) ∙
                            ( left-unit-law-add-Ab (G i) _)))
                      ( Hg i))
                  ( Hf i)))

    is-closed-under-negatives-has-finite-support-type-Π-Ab :
      is-closed-under-negatives-subset-Ab
        ( Π-Ab I G)
        ( has-finite-support-prop-type-Π-Ab)
    is-closed-under-negatives-has-finite-support-type-Π-Ab {f} =
      map-trunc-Prop
        ( tot
          ( λ Ff Hf i →
            map-disjunction
              ( id)
              ( λ fi=0 → ap (neg-Ab (G i)) fi=0 ∙ neg-zero-Ab (G i))
              ( Hf i)))

  is-subgroup-has-finite-support-type-Π-Ab :
    is-subgroup-Ab
      ( Π-Ab I G)
      ( has-finite-support-prop-type-Π-Ab)
  is-subgroup-has-finite-support-type-Π-Ab =
    ( has-finite-support-zero-Π-Ab ,
      is-closed-under-addition-has-finite-support-type-Π-Ab ,
      is-closed-under-negatives-has-finite-support-type-Π-Ab)

  subgroup-has-finite-support-type-Π-Ab :
    Subgroup-Ab (lsuc l1 ⊔ l2) (Π-Ab I G)
  subgroup-has-finite-support-type-Π-Ab =
    ( has-finite-support-prop-type-Π-Ab ,
      is-subgroup-has-finite-support-type-Π-Ab)

  ∑-Ab : Ab (lsuc l1 ⊔ l2)
  ∑-Ab =
    ab-Subgroup-Ab
      ( Π-Ab I G)
      ( subgroup-has-finite-support-type-Π-Ab)

  type-∑-Ab : UU (lsuc l1 ⊔ l2)
  type-∑-Ab = type-Ab ∑-Ab

  add-∑-Ab : type-∑-Ab → type-∑-Ab → type-∑-Ab
  add-∑-Ab = add-Ab ∑-Ab

  pr-type-∑-Ab : type-∑-Ab → (i : I) → type-Ab (G i)
  pr-type-∑-Ab = pr1

  has-finite-support-type-∑-Ab :
    (g : type-∑-Ab) → has-finite-support-type-Π-Ab (pr-type-∑-Ab g)
  has-finite-support-type-∑-Ab = pr2
```

## Properties

### The map of dependent pairs into the direct sum

```agda
module _
  {l1 l2 : Level}
  (I : Set l1)
  (D : has-decidable-equality (type-Set I))
  (G : type-Set I → Ab l2)
  ((i , gᵢ) : Σ (type-Set I) (type-Ab ∘ G))
  where

  map-in-pair-∑-Ab : type-Π-Ab (type-Set I) G
  map-in-pair-∑-Ab i' =
    rec-coproduct
      ( λ i=i' → tr (type-Ab ∘ G) i=i' gᵢ)
      ( λ _ → zero-Ab (G i'))
      ( D i i')

  abstract
    is-zero-map-neq-in-pair-∑-Ab :
      (i' : type-Set I) → i ≠ i' → is-zero-Ab (G i') (map-in-pair-∑-Ab i')
    is-zero-map-neq-in-pair-∑-Ab i' i≠i' with D i i'
    ... | inl i=i' = ex-falso (i≠i' i=i')
    ... | inr _ = refl

  in-pair-∑-Ab : type-∑-Ab (type-Set I) G
  in-pair-∑-Ab =
    ( map-in-pair-∑-Ab ,
      intro-exists
        ( singleton-finitely-enumerable-subtype I i)
        ( λ i' →
          rec-coproduct
            ( λ i=i' → inl-disjunction i=i')
            ( λ i≠i' → inr-disjunction (is-zero-map-neq-in-pair-∑-Ab i' i≠i'))
            ( D i i')))
```

### If `I` is finitely enumerable, the direct sum is isomorphic to the direct product

```agda
module _
  {l1 l2 : Level}
  ((I , is-finitely-enumerable-I) : Finitely-Enumerable-Type l1)
  (G : I → Ab l2)
  where

  is-full-has-finite-support-type-Π-Ab :
    is-full-subtype (has-finite-support-prop-type-Π-Ab I G)
  is-full-has-finite-support-type-Π-Ab f =
    intro-exists
      ( full-subtype l1 I ,
        is-finitely-enumerable-equiv
          ( inv-equiv
            ( equiv-inclusion-is-full-subtype
              ( full-subtype l1 I)
              ( λ _ → raise-star)))
          ( is-finitely-enumerable-I))
      ( λ i' → inl-disjunction raise-star)

  iso-finitely-enumerable-family-∑-Ab-Π-Ab :
    iso-Ab (∑-Ab I G) (Π-Ab I G)
  iso-finitely-enumerable-family-∑-Ab-Π-Ab =
    iso-inclusion-is-full-Subgroup
      ( group-Π-Ab I G)
      ( subgroup-has-finite-support-type-Π-Ab I G)
      ( is-full-has-finite-support-type-Π-Ab)
```

## External links

- [Direct sum of abelian groups](https://en.wikipedia.org/wiki/Direct_sum#Direct_sum_of_abelian_groups)
  on Wikipedia
