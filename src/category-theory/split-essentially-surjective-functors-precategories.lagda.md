# Split essentially surjective functors between precategories

```agda
module category-theory.split-essentially-surjective-functors-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.cores-precategories
open import category-theory.essential-fibers-of-functors-precategories
open import category-theory.essentially-surjective-functors-precategories
open import category-theory.fully-faithful-functors-precategories
open import category-theory.functors-precategories
open import category-theory.isomorphisms-in-categories
open import category-theory.isomorphisms-in-precategories
open import category-theory.precategories
open import category-theory.pseudomonic-functors-precategories

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.retracts-of-types
open import foundation.sections
open import foundation.universe-levels
```

</details>

## Idea

A [functor](category-theory.functors-precategories.md) `F : C → D` between
[precategories](category-theory.precategories.md) is
{{#concept "split essentially surjective" Disambiguation="functor between set-level precategories" Agda=is-split-essentially-surjective-functor-Precategory  Agda=split-essentially-surjective-functor-Precategory}}
if there is a section of the
[essential fiber](category-theory.essential-fibers-of-functors-precategories.md)
over every object of `D`.

## Definitions

### The type of proofs that a functor is split essentially surjective

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2) (D : Precategory l3 l4)
  (F : functor-Precategory C D)
  where

  is-split-essentially-surjective-functor-Precategory : UU (l1 ⊔ l3 ⊔ l4)
  is-split-essentially-surjective-functor-Precategory =
    (y : obj-Precategory D) → essential-fiber-functor-Precategory C D F y

  obj-is-split-essentially-surjective-functor-Precategory :
    is-split-essentially-surjective-functor-Precategory →
    obj-Precategory D → obj-Precategory C
  obj-is-split-essentially-surjective-functor-Precategory
    is-split-ess-surj-F y =
    pr1 (is-split-ess-surj-F y)

  iso-is-split-essentially-surjective-functor-Precategory :
    ( is-split-ess-surj-F :
        is-split-essentially-surjective-functor-Precategory) →
    (y : obj-Precategory D) →
    iso-Precategory D
      ( obj-functor-Precategory C D F
        ( obj-is-split-essentially-surjective-functor-Precategory
          ( is-split-ess-surj-F)
          ( y)))
      ( y)
  iso-is-split-essentially-surjective-functor-Precategory
    is-split-ess-surj-F y =
    pr2 (is-split-ess-surj-F y)
```

We also record a variant with the opposite variance:

```agda
  is-split-essentially-surjective-functor-Precategory' : UU (l1 ⊔ l3 ⊔ l4)
  is-split-essentially-surjective-functor-Precategory' =
    (y : obj-Precategory D) → essential-fiber-functor-Precategory' C D F y

  obj-is-split-essentially-surjective-functor-Precategory' :
    is-split-essentially-surjective-functor-Precategory' →
    obj-Precategory D → obj-Precategory C
  obj-is-split-essentially-surjective-functor-Precategory'
    is-split-ess-surj-F' y =
    pr1 (is-split-ess-surj-F' y)

  iso-is-split-essentially-surjective-functor-Precategory' :
    ( is-split-ess-surj-F' :
        is-split-essentially-surjective-functor-Precategory') →
    (y : obj-Precategory D) →
    iso-Precategory D
      ( y)
      ( obj-functor-Precategory C D F
        ( obj-is-split-essentially-surjective-functor-Precategory'
          ( is-split-ess-surj-F')
          ( y)))
  iso-is-split-essentially-surjective-functor-Precategory'
    is-split-ess-surj-F' y =
    pr2 (is-split-ess-surj-F' y)
```

### The type of split essentially surjective functors

```agda
split-essentially-surjective-functor-Precategory :
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2) (D : Precategory l3 l4) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
split-essentially-surjective-functor-Precategory C D =
  Σ ( functor-Precategory C D)
    ( is-split-essentially-surjective-functor-Precategory C D)

module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2) (D : Precategory l3 l4)
  (F : split-essentially-surjective-functor-Precategory C D)
  where

  functor-split-essentially-surjective-functor-Precategory :
    functor-Precategory C D
  functor-split-essentially-surjective-functor-Precategory = pr1 F

  is-split-essentially-surjective-split-essentially-surjective-functor-Precategory :
    is-split-essentially-surjective-functor-Precategory C D
      ( functor-split-essentially-surjective-functor-Precategory)
  is-split-essentially-surjective-split-essentially-surjective-functor-Precategory =
    pr2 F

  obj-split-essentially-surjective-functor-Precategory :
    obj-Precategory C → obj-Precategory D
  obj-split-essentially-surjective-functor-Precategory =
    obj-functor-Precategory C D
      ( functor-split-essentially-surjective-functor-Precategory)

  hom-split-essentially-surjective-functor-Precategory :
    {x y : obj-Precategory C} →
    hom-Precategory C x y →
    hom-Precategory D
      ( obj-split-essentially-surjective-functor-Precategory x)
      ( obj-split-essentially-surjective-functor-Precategory y)
  hom-split-essentially-surjective-functor-Precategory =
    hom-functor-Precategory C D
      ( functor-split-essentially-surjective-functor-Precategory)
```

## Properties

### Split essentially surjective functors are essentially surjective

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2) (D : Precategory l3 l4)
  where

  is-essentially-surjective-is-split-essentially-surjective-functor-Precategory :
    (F : functor-Precategory C D) →
    is-split-essentially-surjective-functor-Precategory C D F →
    is-essentially-surjective-functor-Precategory C D F
  is-essentially-surjective-is-split-essentially-surjective-functor-Precategory
    F is-split-ess-surj-F =
    unit-trunc-Prop ∘ is-split-ess-surj-F

  essentially-surjective-functor-split-essentially-surjective-functor-Precategory :
    split-essentially-surjective-functor-Precategory C D →
    essentially-surjective-functor-Precategory C D
  essentially-surjective-functor-split-essentially-surjective-functor-Precategory =
    tot
      ( is-essentially-surjective-is-split-essentially-surjective-functor-Precategory)
```

### Being split essentially surjective is a property of fully faithful functors when the domain is a category

This is Lemma 6.8 of {{#cite AKS15}}, although we give a different proof.

**Proof.** Let `F : 𝒞 → 𝒟` be a functor of precategories, where `𝒞` is
univalent. It suffices to assume `F` is fully faithful on isomorphism-sets.
Then, to show that `is-split-essentially-surjective` is a proposition, i.e.,
that

```text
  (d : 𝒟₀) → Σ (x : 𝒞₀), (Fx ≅ d)
```

is a proposition it is equivalent to show that if it has an element it is
contractible, so assume `F` is split essentially surjective. Then, it suffices
to show that for every `d : 𝒟₀`, the type `Σ (x : 𝒞₀), (Fx ≅ d)` is
contractible. By split essential surjectivity there is an element `y : 𝒞₀` such
that `Fy ≅ d` and since postcompositing by an isomorphism is an equivalence of
isomorphism-sets, we have

```text
  (Fx ≅ d) ≃ (Fx ≅ Fy) ≃ (x ≅ y)
```

so `(Σ (x : 𝒞₀), (Fx ≅ d)) ≃ (Σ (x : 𝒞₀), (x ≅ y))`, and the latter is
contractible by univalence.

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2) (D : Precategory l3 l4)
  (F : functor-Precategory C D)
  (c : is-category-Precategory C)
  where

  is-proof-irrelevant-is-split-essentially-surjective-has-section-on-isos-functor-is-category-domain-Precategory :
    ( (x y : obj-Precategory C) →
      section (preserves-iso-functor-Precategory C D F {x} {y})) →
    is-proof-irrelevant
      ( is-split-essentially-surjective-functor-Precategory C D F)
  is-proof-irrelevant-is-split-essentially-surjective-has-section-on-isos-functor-is-category-domain-Precategory
    H s =
    is-contr-Π
      ( λ d →
        is-contr-retract-of
          ( Σ (obj-Category (C , c)) (iso-Category (C , c) (pr1 (s d))))
          ( retract-tot
            ( λ x →
              comp-retract
                ( retract-section
                  ( preserves-iso-functor-Precategory C D F)
                  ( H (pr1 (s d)) x))
                ( retract-equiv
                  ( equiv-inv-iso-Precategory D ∘e
                    equiv-postcomp-hom-iso-Precategory
                      ( core-precategory-Precategory D)
                      ( map-equiv
                        ( compute-iso-core-Precategory D)
                        ( inv-iso-Precategory D (pr2 (s d))))
                      ( obj-functor-Precategory C D F x)))))
          ( is-torsorial-iso-Category (C , c) (pr1 (s d))))

  is-prop-is-split-essentially-surjective-has-section-on-isos-functor-is-category-domain-Precategory :
    ( (x y : obj-Precategory C) →
      section (preserves-iso-functor-Precategory C D F {x} {y})) →
    is-prop
      ( is-split-essentially-surjective-functor-Precategory C D F)
  is-prop-is-split-essentially-surjective-has-section-on-isos-functor-is-category-domain-Precategory
    =
    is-prop-is-proof-irrelevant ∘
    is-proof-irrelevant-is-split-essentially-surjective-has-section-on-isos-functor-is-category-domain-Precategory

  is-prop-is-split-essentially-surjective-is-fully-faithful-on-isos-functor-is-category-domain-Precategory :
    ( (x y : obj-Precategory C) →
      is-equiv (preserves-iso-functor-Precategory C D F {x} {y})) →
    is-prop (is-split-essentially-surjective-functor-Precategory C D F)
  is-prop-is-split-essentially-surjective-is-fully-faithful-on-isos-functor-is-category-domain-Precategory
    H =
    is-prop-is-split-essentially-surjective-has-section-on-isos-functor-is-category-domain-Precategory
      ( λ x y → section-is-equiv (H x y))

  is-prop-is-split-essentially-surjective-is-pseudomonic-functor-is-category-domain-Precategory :
    is-pseudomonic-functor-Precategory C D F →
    is-prop (is-split-essentially-surjective-functor-Precategory C D F)
  is-prop-is-split-essentially-surjective-is-pseudomonic-functor-is-category-domain-Precategory
    H =
    is-prop-is-split-essentially-surjective-is-fully-faithful-on-isos-functor-is-category-domain-Precategory
      ( λ x y →
        is-equiv-preserves-iso-is-pseudomonic-functor-Precategory C D F H
          { x}
          { y})

  is-prop-is-split-essentially-surjective-is-fully-faithful-functor-is-category-domain-Precategory :
    is-fully-faithful-functor-Precategory C D F →
    is-prop (is-split-essentially-surjective-functor-Precategory C D F)
  is-prop-is-split-essentially-surjective-is-fully-faithful-functor-is-category-domain-Precategory
    H =
    is-prop-is-split-essentially-surjective-is-pseudomonic-functor-is-category-domain-Precategory
      ( is-pseudomonic-is-fully-faithful-functor-Precategory C D F H)
```

## References

{{#bibliography}}

## External links

- [Essential Fibres](https://1lab.dev/Cat.Functor.Properties.html#essential-fibres)
  at 1lab
- [split essentially surjective functor](https://ncatlab.org/nlab/show/split+essentially+surjective+functor)
  at $n$Lab

A wikidata identifier was not available for this concept.
