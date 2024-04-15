# Rewriting rules for pushouts

```agda
{-# OPTIONS --rewriting #-}

module synthetic-homotopy-theory.rewriting-pushouts where
```

<details><summary>Imports</summary>

```agda
open import reflection.rewriting
open import foundation.universe-levels
open import foundation.homotopies
open import foundation.identity-types

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.pushouts
```

</details>

## Idea

We endow the eliminator of the
[standard pushouts](synthetic-homotopy-theory.pushouts.md) `cogap` with strict
computation rules on the point constructors using Agda's
[rewriting](reflection.rewriting.md) functionality. This gives us the strict
equalities

```text
  cogap (inl-pushout f g a) ≐ horizontal-map-cocone f g c a
```

and

```text
  cogap (inr-pushout f g b) ≐ vertical-map-cocone f g c b.
```

More generally, we enable strict computation rules for the dependent eliminator,
giving us the strict equalities

```text
  dependent-cogap (inl-pushout f g a) ≐
  horizontal-map-dependent-cocone f g (cocone-pushout f g) P c a
```

and

```text
  dependent-cogap (inr-pushout f g b) ≐
  vertical-map-dependent-cocone f g (cocone-pushout f g) P c b,
```

in such a way that the (pre-existing) witnesses of these equalities reduce to
`refl`. This is achieved using Agda's
[equality erasure](reflection.erasing-equality.md) functionality.

**Note.** By default, we abstain from using rewrite rules in agda-unimath.
However, we recognize their usefulness in, for example, exploratory
formalizations. Since formalizations with and without rewrite rules can coexist,
there is no harm in providing these tools for those that see a need to use them.
We do, however, emphasize that formalizations without the use of rewrite rules
are preferred over those that do use them in the library, as the former can also
be applied in other formalizations that don't enable rewrite rules.

## Rewrite rules

```agda
{-# REWRITE compute-inl-dependent-cogap #-}
{-# REWRITE compute-inr-dependent-cogap #-}
```

## Properties

### Verifying the reduction behavior of the computation rules for the nondependent eliminator of standard pushouts

```agda
module _
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X)
  where

  _ : compute-inl-cogap f g c ~ refl-htpy
  _ = refl-htpy

  _ : compute-inr-cogap f g c ~ refl-htpy
  _ = refl-htpy
```

## See also

- For some discussion on strict computation rules for higher inductive types,
  see the introduction to Section 6.2 of {{#cite UF13}}.

## References

{{#bibliography}} {{#reference UF13}}
