# Identity systems of descent data for pushouts

```agda
{-# OPTIONS --lossy-unification #-}

open import foundation.function-extensionality-axiom

module
  synthetic-homotopy-theory.identity-systems-descent-data-pushouts
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-maps funext
open import foundation.contractible-types funext
open import foundation.dependent-pair-types
open import foundation.equivalences funext
open import foundation.function-types funext
open import foundation.functoriality-dependent-pair-types funext
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies funext
open import foundation.identity-systems
open import foundation.identity-types funext
open import foundation.sections funext
open import foundation.singleton-induction
open import foundation.span-diagrams funext
open import foundation.torsorial-type-families funext
open import foundation.transposition-identifications-along-equivalences funext
open import foundation.universal-property-dependent-pair-types funext
open import foundation.universal-property-identity-types funext
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-spans funext
open import synthetic-homotopy-theory.dependent-universal-property-pushouts funext
open import synthetic-homotopy-theory.descent-data-equivalence-types-over-pushouts funext
open import synthetic-homotopy-theory.descent-data-identity-types-over-pushouts funext
open import synthetic-homotopy-theory.descent-data-pushouts funext
open import synthetic-homotopy-theory.descent-property-pushouts funext
open import synthetic-homotopy-theory.equivalences-descent-data-pushouts funext
open import synthetic-homotopy-theory.families-descent-data-pushouts funext
open import synthetic-homotopy-theory.flattening-lemma-pushouts funext
open import synthetic-homotopy-theory.morphisms-descent-data-pushouts funext
open import synthetic-homotopy-theory.sections-descent-data-pushouts funext
open import synthetic-homotopy-theory.universal-property-pushouts funext
```

</details>

## Idea

We define a universal property of
[descent data](synthetic-homotopy-theory.descent-data-pushouts.md) for the
[identity types](foundation-core.identity-types.md) of
[pushouts](synthetic-homotopy-theory.pushouts.md), which allows their
alternative characterizations. The property is analogous to being an
[identity system](foundation.identity-systems.md); in fact, we show that a type
family over a pushout is an identity system if and only if the corresponding
descent data satisfies this universal property.

Given descent data `(PA, PB, PS)` for the pushout

```text
        g
    S -----> B
    |        |
  f |   H    | j
    ∨        ∨
    A -----> X
        i
```

and a point `p₀ : PA a₀` over a basepoint `a₀ : A`, we would like to mirror the
definition of identity systems. A naïve translation would lead us to define
dependent descent data and its sections. We choose to sidestep building that
technical infrastructure. By the
[descent property](synthetic-homotopy-theory.descent-property-pushouts.md),
there is a [unique](foundation-core.contractible-types.md) type family
`P : X → 𝒰`
[corresponding](synthetic-homotopy-theory.families-descent-data-pushouts.md) to
`(PA, PB, PS)`. Observe that the type of dependent type families
`(x : X) → (p : P x) → 𝒰` is [equivalent](foundation-core.equivalences.md) to
the [uncurried](foundation.universal-property-dependent-pair-types.md) form
`(Σ X P) → 𝒰`. By the
[flattening lemma](synthetic-homotopy-theory.flattening-lemma-pushouts.md), the
total space `Σ X P` is the pushout of the
[span diagram](foundation.span-diagrams.md) of total spaces

```text
  Σ A PA <----- Σ S (PA ∘ f) -----> Σ B PB,
```

so, again by the descent property, descent data over it correspond to type
families over `Σ X P`. Hence we can talk about descent data `(RΣA, RΣB, RΣS)`
over the total span diagram instead of dependent descent data.

Every such descent data induces an evaluation map `ev-refl` on its
[sections](synthetic-homotopy-theory.sections-descent-data-pushouts.md), which
takes a section `(tA, tB, tS)` of `(RΣA, RΣB, RΣS)` to the point
`tA (a₀, p₀) : RΣA (a₀, p₀)`. We say that `(PA, PB, PS)` is an
{{#concept "identity system" Disambiguation="descent data for pushouts" Agda=is-identity-system-descent-data-pushout}}
based at `p₀` if `ev-refl` has a [section](foundation-core.sections.md), in the
sense that there is a converse map
`ind-R : RΣA (a₀, p₀) → section-descent-data (RΣA, RΣB, RΣS)` such that
`(ind-R r)A (a₀, p₀) = r` for all `r : RΣA (a₀, p₀)`. Mind the unfortunate
terminology clash between "sections of descent data" and "sections of a map".

Note that this development is biased towards to left --- we pick a basepoint in
the domain `a₀ : A`, a point in the left type family `p₀ : PA a₀`, and the
evaluation map evaluates the left map of the section. By symmetry of pushouts we
could just as well work with the points `b₀ : B`, `p₀ : PB b₀`, and the
evaluation map evaluating the right map of the section.

By showing that the canonical
[descent data for identity types](synthetic-homotopy-theory.descent-data-identity-types-over-pushouts.md)
is an identity system, we recover the "induction principle for pushout equality"
stated and proved by Kraus and von Raumer in {{#cite KvR19}}.

First observe that the type of sections of the evaluation map is

```text
  Σ (ind-R : (r : RΣA (a₀, p₀)) → section (RΣA, RΣB, RΣS))
    (is-sect : (r : RΣA (a₀, p₀)) → (ind-R r)A (a₀, p₀) = r),
```

which is equivalent to the type

```text
  (r : RΣA (a₀, p₀)) →
  Σ (ind : section (RΣA, RΣB, RΣS))
    (preserves-pt : indA (a₀, p₀) = r)
```

by
[distributivity of Π over Σ](foundation-core.type-theoretic-principle-of-choice.md).

Then the induction terms from {{#cite KvR19}} (with names changed to fit our
naming scheme)

```text
  indᴬ : (a : A) (q : ia₀ = ia) → RΣA (a, q)
  indᴮ : (b : B) (q : ia₀ = jb) → RΣB (b, q)
```

are the first and second components of the section of `(RΣA, RΣB, RΣS)` induced
by `r`, and their computation rules

```text
  indᴬ a₀ refl = r
  (s : S) (q : ia₀ = ifa) → RΣS (s, q) (indᴬ fs q) = indᴮ gs (q ∙ H s)
```

arise as the `preserves-pt` component above, and the coherence condition of a
section of `(RΣA, RΣB, RΣS)`, respectively.

## Definitions

### The evaluation map of a section of descent data for pushouts

```agda
module _
  {l1 l2 l3 l4 : Level} {𝒮 : span-diagram l1 l2 l3}
  (P : descent-data-pushout 𝒮 l4) {a₀ : domain-span-diagram 𝒮}
  (p₀ : left-family-descent-data-pushout P a₀)
  where

  ev-refl-section-descent-data-pushout :
    {l5 : Level}
    (R :
      descent-data-pushout (span-diagram-flattening-descent-data-pushout P) l5)
    (t : section-descent-data-pushout R) →
    left-family-descent-data-pushout R (a₀ , p₀)
  ev-refl-section-descent-data-pushout R t =
    left-map-section-descent-data-pushout R t (a₀ , p₀)
```

### The predicate of being an identity system on descent data for pushouts

```agda
module _
  {l1 l2 l3 l4 : Level} {𝒮 : span-diagram l1 l2 l3}
  (P : descent-data-pushout 𝒮 l4) {a₀ : domain-span-diagram 𝒮}
  (p₀ : left-family-descent-data-pushout P a₀)
  where

  is-identity-system-descent-data-pushout : UUω
  is-identity-system-descent-data-pushout =
    {l5 : Level}
    (R :
      descent-data-pushout
        ( span-diagram-flattening-descent-data-pushout P)
        ( l5)) →
    section (ev-refl-section-descent-data-pushout P p₀ R)
```

## Properties

### A type family over a pushout is an identity system if and only if the corresponding descent data is an identity system

Given a family with descent data `P ≃ (PA, PB, PS)` and a point `p₀ : PA a₀`, we
show that `(PA, PB, PS)` is an identity system at `p₀` if an only if `P` is an
identity system at `(eᴾA a)⁻¹ p₀ : P (ia₀)`.

**Proof:** Consider a family with descent data `RΣ ≈ (RΣA, RΣB, RΣS)`. Recall
that this datum consists of a type family `RΣ : Σ X P → 𝒰`, descent data

```text
  RΣA : Σ A PA → 𝒰
  RΣB : Σ B PB → 𝒰
  RΣS : ((s, p) : (Σ (s : S) (p : PA fs))) → RΣA (fs, p) ≃ RΣB (gs, PS s p),
```

a pair of equivalences

```text
  eᴿA : ((a, p) : Σ A PA) → RΣ (ia, (eᴾA a)⁻¹ p) ≃ RΣA (a, p)
  eᴿB : ((b, p) : Σ B PB) → RΣ (jb, (eᴾB b)⁻¹ p) ≃ RΣB (b, p),
```

and a coherence between them that isn't relevant here. Then there is a
[commuting square](foundation-core.commuting-squares-of-maps.md)

```text
  (x : X) → (p : P x) → RΣ (x, p) ---> (u : Σ X P) → RΣ u ----> section (RΣA, RΣB, RΣS)
                |                                                           |
                | ev-refl ((eᴾA a)⁻¹ p₀)                                    | ev-refl p₀
                |                                                           |
                ∨                                                           ∨
      RΣ (ia₀, (eᴾA a)⁻¹ p₀) ---------------------------------------> RΣA (a₀, p₀).
                                      eᴿA (a₀, p₀)
```

Since the top and bottom maps are equivalences, we get that the left map has a
section if and only if the right map has a section.

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {𝒮 : span-diagram l1 l2 l3}
  {X : UU l4} {c : cocone-span-diagram 𝒮 X}
  (P : family-with-descent-data-pushout c l5)
  {a₀ : domain-span-diagram 𝒮}
  (p₀ : left-family-family-with-descent-data-pushout P a₀)
  where

  private
    cocone-flattening :
      cocone-span-diagram
        ( span-diagram-flattening-descent-data-pushout
          ( descent-data-family-with-descent-data-pushout P))
        ( Σ X (family-cocone-family-with-descent-data-pushout P))
    cocone-flattening =
      cocone-flattening-descent-data-pushout _ _ c
        ( descent-data-family-with-descent-data-pushout P)
        ( family-cocone-family-with-descent-data-pushout P)
        ( inv-equiv-descent-data-family-with-descent-data-pushout P)

  square-ev-refl-section-descent-data-pushout :
    {l5 : Level}
    (R :
      family-with-descent-data-pushout
        ( cocone-flattening-descent-data-pushout _ _ c
          ( descent-data-family-with-descent-data-pushout P)
          ( family-cocone-family-with-descent-data-pushout P)
          ( inv-equiv-descent-data-pushout _ _
            ( equiv-descent-data-family-with-descent-data-pushout P)))
        ( l5)) →
    coherence-square-maps
      ( section-descent-data-section-family-cocone-span-diagram R ∘ ind-Σ)
      ( ev-refl-identity-system
        ( inv-left-map-family-with-descent-data-pushout P a₀ p₀))
      ( ev-refl-section-descent-data-pushout
        ( descent-data-family-with-descent-data-pushout P)
        ( p₀)
        ( descent-data-family-with-descent-data-pushout R))
      ( left-map-family-with-descent-data-pushout R (a₀ , p₀))
  square-ev-refl-section-descent-data-pushout R = refl-htpy
```

To show the forward implication, assume that `(PA, PB, PS)` is an identity
system at `p₀`. We need to show that for every `R : (x : X) (p : P x) → 𝒰`, the
evaluation map `ev-refl ((eᴾA a)⁻¹ p₀)` has a section. By the descent property,
there is unique descent data `(RΣA, RΣB, RΣS)` for the uncurried family
`RΣ := λ (x, p) → R x p`. Then we get the above square, and by assumption the
right map has a section, hence the left map has a section.

```agda
  abstract
    is-identity-system-is-identity-system-descent-data-pushout :
      universal-property-pushout _ _ c →
      is-identity-system-descent-data-pushout
        ( descent-data-family-with-descent-data-pushout P)
        ( p₀) →
      is-identity-system
        ( family-cocone-family-with-descent-data-pushout P)
        ( horizontal-map-cocone _ _ c a₀)
        ( inv-left-map-family-with-descent-data-pushout P a₀ p₀)
    is-identity-system-is-identity-system-descent-data-pushout
      up-c id-system-P {l} R =
      section-left-map-triangle _ _ _
        ( square-ev-refl-section-descent-data-pushout fam-R)
        ( section-is-equiv
          ( is-equiv-comp _ _
            ( is-equiv-ind-Σ)
            ( is-equiv-section-descent-data-section-family-cocone-span-diagram
              ( fam-R)
              ( flattening-lemma-descent-data-pushout _ _ c
                ( descent-data-family-with-descent-data-pushout P)
                ( family-cocone-family-with-descent-data-pushout P)
                ( inv-equiv-descent-data-family-with-descent-data-pushout P)
                ( up-c)))))
        ( id-system-P (descent-data-family-with-descent-data-pushout fam-R))
      where
        fam-R : family-with-descent-data-pushout cocone-flattening l
        fam-R =
          family-with-descent-data-pushout-family-cocone
            ( cocone-flattening)
            ( ind-Σ R)
```

Similarly, assume `P` is an identity system at `(eᴾA a)⁻¹ p₀`, and assume
descent data `(RΣA, RΣB, RΣS)`. There is a unique corresponding type family
`RΣ`. Then the square above commutes, and the left map has a section by
assumption, so the right map has a section.

```agda
  abstract
    is-identity-system-descent-data-pushout-is-identity-system :
      universal-property-pushout _ _ c →
      is-identity-system
        ( family-cocone-family-with-descent-data-pushout P)
        ( horizontal-map-cocone _ _ c a₀)
        ( inv-left-map-family-with-descent-data-pushout P a₀ p₀) →
      is-identity-system-descent-data-pushout
        ( descent-data-family-with-descent-data-pushout P)
        ( p₀)
    is-identity-system-descent-data-pushout-is-identity-system
      up-c id-system-P {l} R =
      section-right-map-triangle _ _ _
        ( square-ev-refl-section-descent-data-pushout fam-R)
        ( section-comp _ _
          ( id-system-P
            ( ev-pair (family-cocone-family-with-descent-data-pushout fam-R)))
          ( section-map-equiv
            ( left-equiv-family-with-descent-data-pushout fam-R (a₀ , p₀))))
      where
        fam-R : family-with-descent-data-pushout cocone-flattening l
        fam-R =
          family-with-descent-data-pushout-descent-data-pushout
            ( flattening-lemma-descent-data-pushout _ _ c
              ( descent-data-family-with-descent-data-pushout P)
              ( family-cocone-family-with-descent-data-pushout P)
              ( inv-equiv-descent-data-family-with-descent-data-pushout P)
              ( up-c))
            ( R)
```

### The canonical descent data for families of identity types is an identity system

**Proof:** By the above property, the descent data `(IA, IB, IS)` is an identity
system at `refl : ia₀ = ia₀` if and only if the corresponding type family
`Id (ia₀) : X → 𝒰` is an identity system at `refl`, which is already
established.

```agda
module _
  {l1 l2 l3 l4 : Level} {𝒮 : span-diagram l1 l2 l3}
  {X : UU l4} {c : cocone-span-diagram 𝒮 X}
  (up-c : universal-property-pushout _ _ c)
  (a₀ : domain-span-diagram 𝒮)
  where

  abstract
    induction-principle-descent-data-pushout-identity-type :
      is-identity-system-descent-data-pushout
        ( descent-data-identity-type-pushout c (horizontal-map-cocone _ _ c a₀))
        ( refl)
    induction-principle-descent-data-pushout-identity-type =
      is-identity-system-descent-data-pushout-is-identity-system
        ( family-with-descent-data-identity-type-pushout c
          ( horizontal-map-cocone _ _ c a₀))
        ( refl)
        ( up-c)
        ( is-identity-system-is-torsorial
          ( horizontal-map-cocone _ _ c a₀)
          ( refl)
          ( is-torsorial-Id _))
```

### Unique uniqueness of identity systems

For any identity system `(PA, PB, PS)` at `p₀`, there is a unique
[equivalence of descent data](synthetic-homotopy-theory.equivalences-descent-data-pushouts.md)
`(IA, IB, IS) ≃ (PA, PB, PS)` sending `refl` to `p₀`.

**Proof:** Consider the unique type family `P : X → 𝒰` corresponding to
`(PA, PB, PS).` The type of point preserving equivalences between `(IA, IB, IS)`
and `(PA, PB, PS)` is equivalent to the type of
[fiberwise equivalences](foundation-core.families-of-equivalences.md)
`(x : X) → (ia₀ = x) ≃ P x` that send `refl` to `(eᴾA a₀)⁻¹ p₀`. To show that
this type is contractible, it suffices to show that `P` is
[torsorial](foundation-core.torsorial-type-families.md). A type family is
torsorial if it is an identity system, and we have shown that `(PA, PB, PS)`
being an identity system implies that `P` is an identity system.

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {𝒮 : span-diagram l1 l2 l3}
  {X : UU l4} {c : cocone-span-diagram 𝒮 X}
  (up-c : universal-property-pushout _ _ c)
  (P : descent-data-pushout 𝒮 l5) {a₀ : domain-span-diagram 𝒮}
  (p₀ : left-family-descent-data-pushout P a₀)
  (id-system-P : is-identity-system-descent-data-pushout P p₀)
  where

  abstract
    unique-uniqueness-identity-system-descent-data-pushout :
      is-contr
        ( Σ ( equiv-descent-data-pushout
              ( descent-data-identity-type-pushout c
                ( horizontal-map-cocone _ _ c a₀))
              ( P))
            ( λ e → left-map-equiv-descent-data-pushout _ _ e a₀ refl ＝ p₀))
    unique-uniqueness-identity-system-descent-data-pushout =
      is-contr-is-equiv'
        ( Σ ( (x : X) →
              (horizontal-map-cocone _ _ c a₀ ＝ x) ≃
              family-cocone-family-with-descent-data-pushout fam-P x)
            ( λ e → map-equiv (e (horizontal-map-cocone _ _ c a₀)) refl ＝ p₀'))
        ( _)
        ( is-equiv-map-Σ _
          ( is-equiv-equiv-descent-data-equiv-family-cocone-span-diagram
            ( family-with-descent-data-identity-type-pushout c
              ( horizontal-map-cocone _ _ c a₀))
            ( fam-P)
            ( up-c))
          ( λ e →
            is-equiv-map-inv-equiv
              ( eq-transpose-equiv
                ( left-equiv-family-with-descent-data-pushout fam-P a₀)
                ( _)
                ( p₀))))
        ( is-torsorial-pointed-fam-equiv-is-torsorial p₀'
          ( is-torsorial-is-identity-system
            ( horizontal-map-cocone _ _ c a₀)
            ( p₀')
            ( is-identity-system-is-identity-system-descent-data-pushout
              ( fam-P)
              ( p₀)
              ( up-c)
              ( id-system-P))))
      where
      fam-P : family-with-descent-data-pushout c l5
      fam-P = family-with-descent-data-pushout-descent-data-pushout up-c P
      p₀' :
        family-cocone-family-with-descent-data-pushout
          ( fam-P)
          ( horizontal-map-cocone _ _ c a₀)
      p₀' =
        map-compute-inv-left-family-cocone-descent-data-pushout up-c P a₀ p₀
```

### Descent data with a converse to the evaluation map of sections of descent data is an identity system

To show that `(PA, PB, PS)` is an identity system at `p₀ : PA a₀`, it suffices
to provide an element of the type `H : RΣA (a₀, p₀) → section (RΣA, RΣB, RΣS)`
for all `(RΣA, RΣB, RΣS)`.

**Proof:** Consider the unique family `P : X → 𝒰` for `(PA, PB, PS)`. It
suffices to show that `P` is an identity system. As above, we can do that by
showing that it is torsorial. By definition, that means that the total space
`Σ X P` is contractible. We can prove that using the property that a type is
contractible if we provide a point, here `(ia₀, (eᴾA a)⁻¹ p₀)`, and a map

```text
  H' : (RΣ : Σ X P → 𝒰) → (r₀ : RΣ (ia₀, (eᴾA a)⁻¹ p₀)) → (u : Σ X P) → RΣ u.
```

Assume such `RΣ` and `r₀`. A section `(u : Σ X P) → RΣ u` is given by a section
of `(RΣA, RΣB, RΣS)`, and we can get one by applying `H` to
`eᴿA (a₀, p₀) r₀ : RΣA (a₀, p₀)`.

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {𝒮 : span-diagram l1 l2 l3}
  {X : UU l4} {c : cocone-span-diagram 𝒮 X}
  (up-c : universal-property-pushout _ _ c)
  (P : descent-data-pushout 𝒮 l5) {a₀ : domain-span-diagram 𝒮}
  (p₀ : left-family-descent-data-pushout P a₀)
  where

  abstract
    is-identity-system-descent-data-pushout-ind-singleton :
      (H :
        {l6 : Level}
        (R :
          descent-data-pushout
            ( span-diagram-flattening-descent-data-pushout P)
            ( l6))
        (r₀ : left-family-descent-data-pushout R (a₀ , p₀)) →
        section-descent-data-pushout R) →
      is-identity-system-descent-data-pushout P p₀
    is-identity-system-descent-data-pushout-ind-singleton H =
      is-identity-system-descent-data-pushout-is-identity-system
        ( family-with-descent-data-pushout-descent-data-pushout up-c P)
        ( p₀)
        ( up-c)
        ( is-identity-system-is-torsorial
          ( horizontal-map-cocone _ _ c a₀)
          ( p₀')
          ( is-contr-ind-singleton _
            ( horizontal-map-cocone _ _ c a₀ , p₀')
            ( λ R r₀ →
              section-family-section-descent-data-pushout
                ( flattening-lemma-descent-data-pushout _ _ c P
                  ( family-cocone-descent-data-pushout up-c P)
                  ( inv-equiv-family-cocone-descent-data-pushout up-c P)
                  ( up-c))
                ( family-with-descent-data-pushout-family-cocone _ R)
                ( H (descent-data-family-cocone-span-diagram _ R) r₀))))
      where
        p₀' :
          family-cocone-descent-data-pushout up-c P
            ( horizontal-map-cocone _ _ c a₀)
        p₀' =
          map-compute-inv-left-family-cocone-descent-data-pushout up-c P a₀ p₀
```
