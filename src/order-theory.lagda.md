# Order theory

## Modules in the order theory namespace

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module order-theory
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where

open import order-theory.accessible-elements-relations funext univalence truncations public
open import order-theory.bottom-elements-large-posets funext univalence truncations public
open import order-theory.bottom-elements-posets funext univalence truncations public
open import order-theory.bottom-elements-preorders funext univalence truncations public
open import order-theory.chains-posets funext univalence truncations public
open import order-theory.chains-preorders funext univalence truncations public
open import order-theory.closure-operators-large-locales funext univalence truncations public
open import order-theory.closure-operators-large-posets funext univalence truncations public
open import order-theory.commuting-squares-of-galois-connections-large-posets funext univalence truncations public
open import order-theory.commuting-squares-of-order-preserving-maps-large-posets funext univalence truncations public
open import order-theory.coverings-locales funext univalence truncations public
open import order-theory.decidable-posets funext univalence truncations public
open import order-theory.decidable-preorders funext univalence truncations public
open import order-theory.decidable-subposets funext univalence truncations public
open import order-theory.decidable-subpreorders funext univalence truncations public
open import order-theory.decidable-total-orders funext univalence truncations public
open import order-theory.decidable-total-preorders funext univalence truncations public
open import order-theory.deflationary-maps-posets funext univalence truncations public
open import order-theory.deflationary-maps-preorders funext univalence truncations public
open import order-theory.dependent-products-large-frames funext univalence truncations public
open import order-theory.dependent-products-large-inflattices funext univalence truncations public
open import order-theory.dependent-products-large-locales funext univalence truncations public
open import order-theory.dependent-products-large-meet-semilattices funext univalence truncations public
open import order-theory.dependent-products-large-posets funext univalence truncations public
open import order-theory.dependent-products-large-preorders funext univalence truncations public
open import order-theory.dependent-products-large-suplattices funext univalence truncations public
open import order-theory.distributive-lattices funext univalence truncations public
open import order-theory.finite-coverings-locales funext univalence truncations public
open import order-theory.finite-posets funext univalence truncations public
open import order-theory.finite-preorders funext univalence truncations public
open import order-theory.finite-total-orders funext univalence truncations public
open import order-theory.finitely-graded-posets funext univalence truncations public
open import order-theory.frames funext univalence truncations public
open import order-theory.galois-connections funext univalence truncations public
open import order-theory.galois-connections-large-posets funext univalence truncations public
open import order-theory.greatest-lower-bounds-large-posets funext univalence truncations public
open import order-theory.greatest-lower-bounds-posets funext univalence truncations public
open import order-theory.homomorphisms-frames funext univalence truncations public
open import order-theory.homomorphisms-large-frames funext univalence truncations public
open import order-theory.homomorphisms-large-locales funext univalence truncations public
open import order-theory.homomorphisms-large-meet-semilattices funext univalence truncations public
open import order-theory.homomorphisms-large-suplattices funext univalence truncations public
open import order-theory.homomorphisms-meet-semilattices funext univalence truncations public
open import order-theory.homomorphisms-meet-suplattices funext univalence truncations public
open import order-theory.homomorphisms-suplattices funext univalence truncations public
open import order-theory.ideals-preorders funext univalence truncations public
open import order-theory.incidence-algebras funext univalence truncations public
open import order-theory.inflationary-maps-posets funext univalence truncations public
open import order-theory.inflationary-maps-preorders funext univalence truncations public
open import order-theory.inflattices funext univalence truncations public
open import order-theory.inhabited-chains-posets funext univalence truncations public
open import order-theory.inhabited-chains-preorders funext univalence truncations public
open import order-theory.inhabited-finite-total-orders funext univalence truncations public
open import order-theory.interval-subposets funext univalence truncations public
open import order-theory.join-preserving-maps-posets funext univalence truncations public
open import order-theory.join-semilattices funext univalence truncations public
open import order-theory.knaster-tarski-fixed-point-theorem funext univalence truncations public
open import order-theory.large-frames funext univalence truncations public
open import order-theory.large-inflattices funext univalence truncations public
open import order-theory.large-join-semilattices funext univalence truncations public
open import order-theory.large-locales funext univalence truncations public
open import order-theory.large-meet-semilattices funext univalence truncations public
open import order-theory.large-meet-subsemilattices funext univalence truncations public
open import order-theory.large-posets funext univalence truncations public
open import order-theory.large-preorders funext univalence truncations public
open import order-theory.large-quotient-locales funext univalence truncations public
open import order-theory.large-subframes funext univalence truncations public
open import order-theory.large-subposets funext univalence truncations public
open import order-theory.large-subpreorders funext univalence truncations public
open import order-theory.large-subsuplattices funext univalence truncations public
open import order-theory.large-suplattices funext univalence truncations public
open import order-theory.lattices funext univalence truncations public
open import order-theory.least-upper-bounds-large-posets funext univalence truncations public
open import order-theory.least-upper-bounds-posets funext univalence truncations public
open import order-theory.locales funext univalence truncations public
open import order-theory.locally-finite-posets funext univalence truncations public
open import order-theory.lower-bounds-large-posets funext univalence truncations public
open import order-theory.lower-bounds-posets funext univalence truncations public
open import order-theory.lower-sets-large-posets funext univalence truncations public
open import order-theory.lower-types-preorders funext univalence truncations public
open import order-theory.maximal-chains-posets funext univalence truncations public
open import order-theory.maximal-chains-preorders funext univalence truncations public
open import order-theory.meet-semilattices funext univalence truncations public
open import order-theory.meet-suplattices funext univalence truncations public
open import order-theory.nuclei-large-locales funext univalence truncations public
open import order-theory.opposite-large-posets funext univalence truncations public
open import order-theory.opposite-large-preorders funext univalence truncations public
open import order-theory.opposite-posets funext univalence truncations public
open import order-theory.opposite-preorders funext univalence truncations public
open import order-theory.order-preserving-maps-large-posets funext univalence truncations public
open import order-theory.order-preserving-maps-large-preorders funext univalence truncations public
open import order-theory.order-preserving-maps-posets funext univalence truncations public
open import order-theory.order-preserving-maps-preorders funext univalence truncations public
open import order-theory.ordinals funext univalence truncations public
open import order-theory.posets funext univalence truncations public
open import order-theory.powers-of-large-locales funext univalence truncations public
open import order-theory.precategory-of-decidable-total-orders funext univalence truncations public
open import order-theory.precategory-of-finite-posets funext univalence truncations public
open import order-theory.precategory-of-finite-total-orders funext univalence truncations public
open import order-theory.precategory-of-inhabited-finite-total-orders funext univalence truncations public
open import order-theory.precategory-of-posets funext univalence truncations public
open import order-theory.precategory-of-total-orders funext univalence truncations public
open import order-theory.preorders funext univalence truncations public
open import order-theory.principal-lower-sets-large-posets funext univalence truncations public
open import order-theory.principal-upper-sets-large-posets funext univalence truncations public
open import order-theory.reflective-galois-connections-large-posets funext univalence truncations public
open import order-theory.resizing-posets funext univalence truncations public
open import order-theory.resizing-preorders funext univalence truncations public
open import order-theory.resizing-suplattices funext univalence truncations public
open import order-theory.similarity-of-elements-large-posets funext univalence truncations public
open import order-theory.similarity-of-elements-large-preorders funext univalence truncations public
open import order-theory.similarity-of-order-preserving-maps-large-posets funext univalence truncations public
open import order-theory.similarity-of-order-preserving-maps-large-preorders funext univalence truncations public
open import order-theory.strict-order-preserving-maps funext univalence truncations public
open import order-theory.strict-preorders funext univalence truncations public
open import order-theory.strictly-inflationary-maps-strict-preorders funext univalence truncations public
open import order-theory.strictly-preordered-sets funext univalence truncations public
open import order-theory.subposets funext univalence truncations public
open import order-theory.subpreorders funext univalence truncations public
open import order-theory.suplattices funext univalence truncations public
open import order-theory.supremum-preserving-maps-posets funext univalence truncations public
open import order-theory.top-elements-large-posets funext univalence truncations public
open import order-theory.top-elements-posets funext univalence truncations public
open import order-theory.top-elements-preorders funext univalence truncations public
open import order-theory.total-orders funext univalence truncations public
open import order-theory.total-preorders funext univalence truncations public
open import order-theory.transitive-well-founded-relations funext univalence truncations public
open import order-theory.transposition-inequalities-along-order-preserving-retractions-posets funext univalence truncations public
open import order-theory.transposition-inequalities-along-sections-of-order-preserving-maps-posets funext univalence truncations public
open import order-theory.upper-bounds-chains-posets funext univalence truncations public
open import order-theory.upper-bounds-large-posets funext univalence truncations public
open import order-theory.upper-bounds-posets funext univalence truncations public
open import order-theory.upper-sets-large-posets funext univalence truncations public
open import order-theory.well-founded-relations funext univalence truncations public
open import order-theory.zorns-lemma funext univalence truncations public
```
