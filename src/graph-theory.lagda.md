# Graph theory

## Modules in the graph theory namespace

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module graph-theory
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where

open import graph-theory.acyclic-undirected-graphs funext univalence truncations public
open import graph-theory.base-change-dependent-directed-graphs funext univalence truncations public
open import graph-theory.base-change-dependent-reflexive-graphs funext univalence truncations public
open import graph-theory.cartesian-products-directed-graphs funext univalence truncations public
open import graph-theory.cartesian-products-reflexive-graphs funext univalence truncations public
open import graph-theory.circuits-undirected-graphs funext univalence truncations public
open import graph-theory.closed-walks-undirected-graphs funext univalence truncations public
open import graph-theory.complete-bipartite-graphs funext univalence truncations public
open import graph-theory.complete-multipartite-graphs funext univalence truncations public
open import graph-theory.complete-undirected-graphs funext univalence truncations public
open import graph-theory.connected-undirected-graphs funext univalence truncations public
open import graph-theory.cycles-undirected-graphs funext univalence truncations public
open import graph-theory.dependent-directed-graphs funext univalence public
open import graph-theory.dependent-products-directed-graphs funext univalence truncations public
open import graph-theory.dependent-products-reflexive-graphs funext univalence truncations public
open import graph-theory.dependent-reflexive-graphs funext univalence truncations public
open import graph-theory.dependent-sums-directed-graphs funext univalence truncations public
open import graph-theory.dependent-sums-reflexive-graphs funext univalence truncations public
open import graph-theory.directed-graph-duality funext univalence truncations public
open import graph-theory.directed-graph-structures-on-standard-finite-sets funext univalence truncations public
open import graph-theory.directed-graphs funext univalence public
open import graph-theory.discrete-dependent-reflexive-graphs funext univalence truncations public
open import graph-theory.discrete-directed-graphs funext univalence truncations public
open import graph-theory.discrete-reflexive-graphs funext univalence truncations public
open import graph-theory.displayed-large-reflexive-graphs funext univalence truncations public
open import graph-theory.edge-coloured-undirected-graphs funext univalence truncations public
open import graph-theory.embeddings-directed-graphs funext univalence truncations public
open import graph-theory.embeddings-undirected-graphs funext univalence truncations public
open import graph-theory.enriched-undirected-graphs funext univalence truncations public
open import graph-theory.equivalences-dependent-directed-graphs funext univalence truncations public
open import graph-theory.equivalences-dependent-reflexive-graphs funext univalence truncations public
open import graph-theory.equivalences-directed-graphs funext univalence truncations public
open import graph-theory.equivalences-enriched-undirected-graphs funext univalence truncations public
open import graph-theory.equivalences-reflexive-graphs funext univalence truncations public
open import graph-theory.equivalences-undirected-graphs funext univalence truncations public
open import graph-theory.eulerian-circuits-undirected-graphs funext univalence truncations public
open import graph-theory.faithful-morphisms-undirected-graphs funext univalence truncations public
open import graph-theory.fibers-directed-graphs funext univalence truncations public
open import graph-theory.fibers-morphisms-directed-graphs funext univalence truncations public
open import graph-theory.fibers-morphisms-reflexive-graphs funext univalence truncations public
open import graph-theory.finite-graphs funext univalence truncations public
open import graph-theory.geometric-realizations-undirected-graphs funext univalence truncations public
open import graph-theory.higher-directed-graphs funext univalence truncations public
open import graph-theory.hypergraphs funext univalence truncations public
open import graph-theory.internal-hom-directed-graphs funext univalence truncations public
open import graph-theory.large-higher-directed-graphs funext univalence truncations public
open import graph-theory.large-reflexive-graphs public
open import graph-theory.matchings funext univalence truncations public
open import graph-theory.mere-equivalences-undirected-graphs funext univalence truncations public
open import graph-theory.morphisms-dependent-directed-graphs funext univalence public
open import graph-theory.morphisms-directed-graphs funext univalence truncations public
open import graph-theory.morphisms-reflexive-graphs funext univalence truncations public
open import graph-theory.morphisms-undirected-graphs funext univalence truncations public
open import graph-theory.neighbors-undirected-graphs funext univalence truncations public
open import graph-theory.orientations-undirected-graphs funext univalence truncations public
open import graph-theory.paths-undirected-graphs funext univalence truncations public
open import graph-theory.polygons funext univalence truncations public
open import graph-theory.raising-universe-levels-directed-graphs funext univalence truncations public
open import graph-theory.reflecting-maps-undirected-graphs funext univalence truncations public
open import graph-theory.reflexive-graphs funext univalence truncations public
open import graph-theory.regular-undirected-graphs funext univalence truncations public
open import graph-theory.sections-dependent-directed-graphs funext univalence truncations public
open import graph-theory.sections-dependent-reflexive-graphs funext univalence truncations public
open import graph-theory.simple-undirected-graphs funext univalence truncations public
open import graph-theory.stereoisomerism-enriched-undirected-graphs funext univalence truncations public
open import graph-theory.terminal-directed-graphs funext univalence truncations public
open import graph-theory.terminal-reflexive-graphs funext univalence truncations public
open import graph-theory.totally-faithful-morphisms-undirected-graphs funext univalence truncations public
open import graph-theory.trails-directed-graphs funext univalence truncations public
open import graph-theory.trails-undirected-graphs funext univalence truncations public
open import graph-theory.undirected-graph-structures-on-standard-finite-sets funext univalence truncations public
open import graph-theory.undirected-graphs funext univalence truncations public
open import graph-theory.universal-directed-graph funext univalence truncations public
open import graph-theory.universal-reflexive-graph funext univalence truncations public
open import graph-theory.vertex-covers funext univalence truncations public
open import graph-theory.voltage-graphs funext univalence truncations public
open import graph-theory.walks-directed-graphs funext univalence truncations public
open import graph-theory.walks-undirected-graphs funext univalence truncations public
open import graph-theory.wide-displayed-large-reflexive-graphs funext univalence truncations public
```
