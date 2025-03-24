# Synthetic homotopy theory

```agda
{-# OPTIONS --rewriting --guardedness #-}
```

## Modules in the synthetic homotopy theory namespace

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module synthetic-homotopy-theory
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where

open import synthetic-homotopy-theory.0-acyclic-maps funext univalence truncations public
open import synthetic-homotopy-theory.0-acyclic-types funext univalence truncations public
open import synthetic-homotopy-theory.1-acyclic-types funext univalence truncations public
open import synthetic-homotopy-theory.acyclic-maps funext univalence truncations public
open import synthetic-homotopy-theory.acyclic-types funext univalence truncations public
open import synthetic-homotopy-theory.category-of-connected-set-bundles-circle funext univalence truncations public
open import synthetic-homotopy-theory.cavallos-trick funext univalence truncations public
open import synthetic-homotopy-theory.circle funext univalence truncations public
open import synthetic-homotopy-theory.cocartesian-morphisms-arrows funext univalence truncations public
open import synthetic-homotopy-theory.cocones-under-pointed-span-diagrams funext univalence truncations public
open import synthetic-homotopy-theory.cocones-under-sequential-diagrams funext univalence truncations public
open import synthetic-homotopy-theory.cocones-under-spans funext public
open import synthetic-homotopy-theory.codiagonals-of-maps funext univalence truncations public
open import synthetic-homotopy-theory.coequalizers funext univalence truncations public
open import synthetic-homotopy-theory.cofibers-of-maps funext univalence truncations public
open import synthetic-homotopy-theory.cofibers-of-pointed-maps funext univalence truncations public
open import synthetic-homotopy-theory.coforks funext univalence truncations public
open import synthetic-homotopy-theory.coforks-cocones-under-sequential-diagrams funext univalence truncations public
open import synthetic-homotopy-theory.conjugation-loops funext univalence truncations public
open import synthetic-homotopy-theory.connected-set-bundles-circle funext univalence truncations public
open import synthetic-homotopy-theory.connective-prespectra funext univalence truncations public
open import synthetic-homotopy-theory.connective-spectra funext univalence truncations public
open import synthetic-homotopy-theory.dependent-cocones-under-sequential-diagrams funext univalence truncations public
open import synthetic-homotopy-theory.dependent-cocones-under-spans funext univalence truncations public
open import synthetic-homotopy-theory.dependent-coforks funext univalence truncations public
open import synthetic-homotopy-theory.dependent-descent-circle funext univalence truncations public
open import synthetic-homotopy-theory.dependent-pullback-property-pushouts funext univalence truncations public
open import synthetic-homotopy-theory.dependent-pushout-products funext univalence truncations public
open import synthetic-homotopy-theory.dependent-sequential-diagrams funext univalence public
open import synthetic-homotopy-theory.dependent-suspension-structures funext univalence truncations public
open import synthetic-homotopy-theory.dependent-universal-property-coequalizers funext univalence truncations public
open import synthetic-homotopy-theory.dependent-universal-property-pushouts funext univalence truncations public
open import synthetic-homotopy-theory.dependent-universal-property-sequential-colimits funext univalence truncations public
open import synthetic-homotopy-theory.dependent-universal-property-suspensions funext univalence truncations public
open import synthetic-homotopy-theory.descent-circle funext univalence truncations public
open import synthetic-homotopy-theory.descent-circle-constant-families funext univalence truncations public
open import synthetic-homotopy-theory.descent-circle-dependent-pair-types funext univalence truncations public
open import synthetic-homotopy-theory.descent-circle-equivalence-types funext univalence truncations public
open import synthetic-homotopy-theory.descent-circle-function-types funext univalence truncations public
open import synthetic-homotopy-theory.descent-circle-subtypes funext univalence truncations public
open import synthetic-homotopy-theory.descent-data-equivalence-types-over-pushouts funext univalence truncations public
open import synthetic-homotopy-theory.descent-data-function-types-over-pushouts funext univalence truncations public
open import synthetic-homotopy-theory.descent-data-identity-types-over-pushouts funext univalence truncations public
open import synthetic-homotopy-theory.descent-data-pushouts funext public
open import synthetic-homotopy-theory.descent-data-sequential-colimits funext univalence truncations public
open import synthetic-homotopy-theory.descent-property-pushouts funext univalence truncations public
open import synthetic-homotopy-theory.descent-property-sequential-colimits funext univalence truncations public
open import synthetic-homotopy-theory.double-loop-spaces funext univalence truncations public
open import synthetic-homotopy-theory.eckmann-hilton-argument funext univalence truncations public
open import synthetic-homotopy-theory.equifibered-sequential-diagrams funext univalence public
open import synthetic-homotopy-theory.equivalences-cocones-under-equivalences-sequential-diagrams funext univalence truncations public
open import synthetic-homotopy-theory.equivalences-coforks-under-equivalences-double-arrows funext univalence truncations public
open import synthetic-homotopy-theory.equivalences-dependent-sequential-diagrams funext univalence truncations public
open import synthetic-homotopy-theory.equivalences-descent-data-pushouts funext univalence truncations public
open import synthetic-homotopy-theory.equivalences-sequential-diagrams funext univalence truncations public
open import synthetic-homotopy-theory.families-descent-data-pushouts funext univalence truncations public
open import synthetic-homotopy-theory.families-descent-data-sequential-colimits funext univalence truncations public
open import synthetic-homotopy-theory.flattening-lemma-coequalizers funext univalence truncations public
open import synthetic-homotopy-theory.flattening-lemma-pushouts funext univalence truncations public
open import synthetic-homotopy-theory.flattening-lemma-sequential-colimits funext univalence truncations public
open import synthetic-homotopy-theory.free-loops funext univalence truncations public
open import synthetic-homotopy-theory.functoriality-loop-spaces funext univalence truncations public
open import synthetic-homotopy-theory.functoriality-sequential-colimits funext univalence truncations public
open import synthetic-homotopy-theory.functoriality-suspensions funext univalence truncations public
open import synthetic-homotopy-theory.groups-of-loops-in-1-types funext univalence truncations public
open import synthetic-homotopy-theory.hatchers-acyclic-type funext univalence truncations public
open import synthetic-homotopy-theory.homotopy-groups funext univalence truncations public
open import synthetic-homotopy-theory.identity-systems-descent-data-pushouts funext univalence truncations public
open import synthetic-homotopy-theory.induction-principle-pushouts funext univalence truncations public
open import synthetic-homotopy-theory.infinite-complex-projective-space funext univalence truncations public
open import synthetic-homotopy-theory.infinite-cyclic-types funext univalence truncations public
open import synthetic-homotopy-theory.interval-type funext univalence public
open import synthetic-homotopy-theory.iterated-loop-spaces funext univalence truncations public
open import synthetic-homotopy-theory.iterated-suspensions-of-pointed-types funext univalence truncations public
open import synthetic-homotopy-theory.join-powers-of-types funext univalence truncations public
open import synthetic-homotopy-theory.joins-of-maps funext univalence truncations public
open import synthetic-homotopy-theory.joins-of-types funext univalence truncations public
open import synthetic-homotopy-theory.left-half-smash-products funext univalence truncations public
open import synthetic-homotopy-theory.loop-homotopy-circle funext univalence truncations public
open import synthetic-homotopy-theory.loop-spaces funext univalence truncations public
open import synthetic-homotopy-theory.maps-of-prespectra funext univalence truncations public
open import synthetic-homotopy-theory.mere-spheres funext univalence truncations public
open import synthetic-homotopy-theory.morphisms-cocones-under-morphisms-sequential-diagrams funext univalence truncations public
open import synthetic-homotopy-theory.morphisms-coforks-under-morphisms-double-arrows funext univalence truncations public
open import synthetic-homotopy-theory.morphisms-dependent-sequential-diagrams funext univalence public
open import synthetic-homotopy-theory.morphisms-descent-data-circle funext univalence truncations public
open import synthetic-homotopy-theory.morphisms-descent-data-pushouts funext univalence truncations public
open import synthetic-homotopy-theory.morphisms-sequential-diagrams funext univalence truncations public
open import synthetic-homotopy-theory.multiplication-circle funext univalence truncations public
open import synthetic-homotopy-theory.null-cocones-under-pointed-span-diagrams funext univalence truncations public
open import synthetic-homotopy-theory.plus-principle funext univalence truncations public
open import synthetic-homotopy-theory.powers-of-loops funext univalence truncations public
open import synthetic-homotopy-theory.premanifolds funext univalence truncations public
open import synthetic-homotopy-theory.prespectra funext univalence truncations public
open import synthetic-homotopy-theory.pullback-property-pushouts funext univalence truncations public
open import synthetic-homotopy-theory.pushout-products funext univalence truncations public
open import synthetic-homotopy-theory.pushouts funext univalence truncations public
open import synthetic-homotopy-theory.pushouts-of-pointed-types funext univalence truncations public
open import synthetic-homotopy-theory.recursion-principle-pushouts funext univalence truncations public
open import synthetic-homotopy-theory.retracts-of-sequential-diagrams funext univalence truncations public
open import synthetic-homotopy-theory.rewriting-pushouts funext univalence truncations public
open import synthetic-homotopy-theory.sections-descent-circle funext univalence truncations public
open import synthetic-homotopy-theory.sections-descent-data-pushouts funext univalence truncations public
open import synthetic-homotopy-theory.sequential-colimits funext univalence truncations public
open import synthetic-homotopy-theory.sequential-diagrams funext univalence public
open import synthetic-homotopy-theory.sequentially-compact-types funext univalence truncations public
open import synthetic-homotopy-theory.shifts-sequential-diagrams funext univalence truncations public
open import synthetic-homotopy-theory.smash-products-of-pointed-types funext univalence truncations public
open import synthetic-homotopy-theory.spectra funext univalence truncations public
open import synthetic-homotopy-theory.sphere-prespectrum funext univalence truncations public
open import synthetic-homotopy-theory.spheres funext univalence truncations public
open import synthetic-homotopy-theory.suspension-prespectra funext univalence truncations public
open import synthetic-homotopy-theory.suspension-structures funext univalence truncations public
open import synthetic-homotopy-theory.suspensions-of-pointed-types funext univalence truncations public
open import synthetic-homotopy-theory.suspensions-of-propositions funext univalence truncations public
open import synthetic-homotopy-theory.suspensions-of-types funext univalence truncations public
open import synthetic-homotopy-theory.tangent-spheres funext univalence truncations public
open import synthetic-homotopy-theory.total-cocones-families-sequential-diagrams funext univalence truncations public
open import synthetic-homotopy-theory.total-sequential-diagrams funext univalence truncations public
open import synthetic-homotopy-theory.triple-loop-spaces funext univalence truncations public
open import synthetic-homotopy-theory.truncated-acyclic-maps funext univalence truncations public
open import synthetic-homotopy-theory.truncated-acyclic-types funext univalence truncations public
open import synthetic-homotopy-theory.universal-cover-circle funext univalence truncations public
open import synthetic-homotopy-theory.universal-property-circle funext univalence truncations public
open import synthetic-homotopy-theory.universal-property-coequalizers funext univalence truncations public
open import synthetic-homotopy-theory.universal-property-pushouts funext univalence truncations public
open import synthetic-homotopy-theory.universal-property-sequential-colimits funext univalence truncations public
open import synthetic-homotopy-theory.universal-property-suspensions funext univalence truncations public
open import synthetic-homotopy-theory.universal-property-suspensions-of-pointed-types funext univalence truncations public
open import synthetic-homotopy-theory.wedges-of-pointed-types funext univalence truncations public
open import synthetic-homotopy-theory.zigzags-sequential-diagrams funext univalence truncations public
```
