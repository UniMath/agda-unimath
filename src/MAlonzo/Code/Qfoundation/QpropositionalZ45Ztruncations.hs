{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qequivalences
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qfunctions
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qpropositions
import qualified MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels
import qualified MAlonzo.Code.Qfoundation.QfunctorialityZ45ZcartesianZ45ZproductZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.Qtruncations
import qualified MAlonzo.Code.Qfoundation.QuniversalZ45ZpropertyZ45ZpropositionalZ45Ztruncation

-- foundation.propositional-truncations.type-trunc-Prop
d_type'45'trunc'45'Prop_6 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> () -> ()
d_type'45'trunc'45'Prop_6 = erased
-- foundation.propositional-truncations.unit-trunc-Prop
d_unit'45'trunc'45'Prop_12 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> () -> AgdaAny -> AgdaAny
d_unit'45'trunc'45'Prop_12 v0 ~v1 = du_unit'45'trunc'45'Prop_12 v0
du_unit'45'trunc'45'Prop_12 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> AgdaAny -> AgdaAny
du_unit'45'trunc'45'Prop_12 v0
  = coe
      MAlonzo.Code.Qfoundation.Qtruncations.d_unit'45'trunc_38 v0
      MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.d_neg'45'one'45'𝕋_10
      erased
-- foundation.propositional-truncations.is-prop-type-trunc-Prop
d_is'45'prop'45'type'45'trunc'45'Prop_18 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'prop'45'type'45'trunc'45'Prop_18 v0 ~v1
  = du_is'45'prop'45'type'45'trunc'45'Prop_18 v0
du_is'45'prop'45'type'45'trunc'45'Prop_18 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'prop'45'type'45'trunc'45'Prop_18 v0
  = coe
      MAlonzo.Code.Qfoundation.Qtruncations.d_is'45'trunc'45'type'45'trunc_16
      v0
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.C_succ'45'𝕋_8
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.C_neg'45'two'45'𝕋_6))
      erased
-- foundation.propositional-truncations.all-elements-equal-type-trunc-Prop
d_all'45'elements'45'equal'45'type'45'trunc'45'Prop_24 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_all'45'elements'45'equal'45'type'45'trunc'45'Prop_24 = erased
-- foundation.propositional-truncations.trunc-Prop
d_trunc'45'Prop_32 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_trunc'45'Prop_32 v0 v1
  = coe
      MAlonzo.Code.Qfoundation.Qtruncations.du_trunc_22 (coe v0)
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.d_neg'45'one'45'𝕋_10)
-- foundation.propositional-truncations.is-prop-condition-ind-trunc-Prop'
d_is'45'prop'45'condition'45'ind'45'trunc'45'Prop''_52 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'prop'45'condition'45'ind'45'trunc'45'Prop''_52 ~v0 ~v1 ~v2
                                                       ~v3 ~v4 ~v5
  = du_is'45'prop'45'condition'45'ind'45'trunc'45'Prop''_52
du_is'45'prop'45'condition'45'ind'45'trunc'45'Prop''_52 ::
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'prop'45'condition'45'ind'45'trunc'45'Prop''_52 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qpropositions.du_is'45'prop'45'all'45'elements'45'equal_70
-- foundation.propositional-truncations.ind-trunc-Prop'
d_ind'45'trunc'45'Prop''_90 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10) ->
  AgdaAny -> AgdaAny
d_ind'45'trunc'45'Prop''_90 ~v0 v1 ~v2 v3 v4 ~v5
  = du_ind'45'trunc'45'Prop''_90 v1 v3 v4
du_ind'45'trunc'45'Prop''_90 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (AgdaAny -> ()) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_ind'45'trunc'45'Prop''_90 v0 v1 v2
  = coe
      MAlonzo.Code.Qfoundation.Qtruncations.du_apply'45'dependent'45'universal'45'property'45'trunc_154
      v0
      MAlonzo.Code.QfoundationZ45Zcore.QtruncationZ45Zlevels.d_neg'45'one'45'𝕋_10
      (\ v3 ->
         coe
           MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
           (coe v1 v3)
           (coe du_is'45'prop'45'condition'45'ind'45'trunc'45'Prop''_52))
      v2
-- foundation.propositional-truncations.ind-trunc-Prop
d_ind'45'trunc'45'Prop_112 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_ind'45'trunc'45'Prop_112 ~v0 v1 ~v2 ~v3 v4
  = du_ind'45'trunc'45'Prop_112 v1 v4
du_ind'45'trunc'45'Prop_112 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_ind'45'trunc'45'Prop_112 v0 v1
  = coe du_ind'45'trunc'45'Prop''_90 (coe v0) erased (coe v1)
-- foundation.propositional-truncations.comp-trunc-Prop
d_comp'45'trunc'45'Prop_134 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_comp'45'trunc'45'Prop_134 = erased
-- foundation.propositional-truncations.is-propositional-truncation-trunc-Prop
d_is'45'propositional'45'truncation'45'trunc'45'Prop_148 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'propositional'45'truncation'45'trunc'45'Prop_148 v0 v1 ~v2
  = du_is'45'propositional'45'truncation'45'trunc'45'Prop_148 v0 v1
du_is'45'propositional'45'truncation'45'trunc'45'Prop_148 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'propositional'45'truncation'45'trunc'45'Prop_148 v0 v1
  = coe
      MAlonzo.Code.Qfoundation.QuniversalZ45ZpropertyZ45ZpropositionalZ45Ztruncation.du_is'45'propositional'45'truncation'45'extension'45'property_260
      (coe (\ v2 v3 -> coe du_ind'45'trunc'45'Prop_112 (coe v0)))
      (coe v1)
-- foundation.propositional-truncations.universal-property-trunc-Prop
d_universal'45'property'45'trunc'45'Prop_164 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_universal'45'property'45'trunc'45'Prop_164 v0 v1 ~v2
  = du_universal'45'property'45'trunc'45'Prop_164 v0 v1
du_universal'45'property'45'trunc'45'Prop_164 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_universal'45'property'45'trunc'45'Prop_164 v0 v1
  = coe
      MAlonzo.Code.Qfoundation.QuniversalZ45ZpropertyZ45ZpropositionalZ45Ztruncation.du_universal'45'property'45'is'45'propositional'45'truncation_136
      (coe v1) (coe v0) (coe du_unit'45'trunc'45'Prop_12 (coe v0))
      (coe
         du_is'45'propositional'45'truncation'45'trunc'45'Prop_148 (coe v0)
         (coe v1))
-- foundation.propositional-truncations.map-universal-property-trunc-Prop
d_map'45'universal'45'property'45'trunc'45'Prop_176 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_map'45'universal'45'property'45'trunc'45'Prop_176 v0 v1 ~v2 v3 v4
  = du_map'45'universal'45'property'45'trunc'45'Prop_176 v0 v1 v3 v4
du_map'45'universal'45'property'45'trunc'45'Prop_176 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_map'45'universal'45'property'45'trunc'45'Prop_176 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Qfoundation.QuniversalZ45ZpropertyZ45ZpropositionalZ45Ztruncation.du_map'45'is'45'propositional'45'truncation_172
      (coe v0) (coe v1) (coe du_unit'45'trunc'45'Prop_12 (coe v0))
      (coe
         (\ v4 ->
            coe
              du_is'45'propositional'45'truncation'45'trunc'45'Prop_148 (coe v0)
              (coe v4)))
      (coe v2) (coe v3)
-- foundation.propositional-truncations.apply-universal-property-trunc-Prop
d_apply'45'universal'45'property'45'trunc'45'Prop_194 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) -> AgdaAny
d_apply'45'universal'45'property'45'trunc'45'Prop_194 v0 v1 ~v2 v3
                                                      v4 v5
  = du_apply'45'universal'45'property'45'trunc'45'Prop_194
      v0 v1 v3 v4 v5
du_apply'45'universal'45'property'45'trunc'45'Prop_194 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny -> AgdaAny) -> AgdaAny
du_apply'45'universal'45'property'45'trunc'45'Prop_194 v0 v1 v2 v3
                                                       v4
  = coe
      du_map'45'universal'45'property'45'trunc'45'Prop_176 v0 v1 v3 v4 v2
-- foundation.propositional-truncations._.map-idempotent-trunc-Prop
d_map'45'idempotent'45'trunc'45'Prop_210 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> () -> AgdaAny -> AgdaAny
d_map'45'idempotent'45'trunc'45'Prop_210 v0 ~v1
  = du_map'45'idempotent'45'trunc'45'Prop_210 v0
du_map'45'idempotent'45'trunc'45'Prop_210 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 -> AgdaAny -> AgdaAny
du_map'45'idempotent'45'trunc'45'Prop_210 v0
  = coe
      du_map'45'universal'45'property'45'trunc'45'Prop_176 (coe v0)
      (coe v0) (coe d_trunc'45'Prop_32 v0 erased) (coe (\ v1 -> v1))
-- foundation.propositional-truncations._.is-equiv-map-idempotent-trunc-Prop
d_is'45'equiv'45'map'45'idempotent'45'trunc'45'Prop_212 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'map'45'idempotent'45'trunc'45'Prop_212 v0 ~v1
  = du_is'45'equiv'45'map'45'idempotent'45'trunc'45'Prop_212 v0
du_is'45'equiv'45'map'45'idempotent'45'trunc'45'Prop_212 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'map'45'idempotent'45'trunc'45'Prop_212 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qpropositions.du_is'45'equiv'45'is'45'prop_140
      (coe du_unit'45'trunc'45'Prop_12 (coe v0))
-- foundation.propositional-truncations._.idempotent-trunc-Prop
d_idempotent'45'trunc'45'Prop_214 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_idempotent'45'trunc'45'Prop_214 v0 ~v1
  = du_idempotent'45'trunc'45'Prop_214 v0
du_idempotent'45'trunc'45'Prop_214 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_idempotent'45'trunc'45'Prop_214 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe du_map'45'idempotent'45'trunc'45'Prop_210 (coe v0))
      (coe
         du_is'45'equiv'45'map'45'idempotent'45'trunc'45'Prop_212 (coe v0))
-- foundation.propositional-truncations._.is-equiv-map-inv-idempotent-trunc-Prop
d_is'45'equiv'45'map'45'inv'45'idempotent'45'trunc'45'Prop_216 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'map'45'inv'45'idempotent'45'trunc'45'Prop_216 v0
                                                               ~v1
  = du_is'45'equiv'45'map'45'inv'45'idempotent'45'trunc'45'Prop_216
      v0
du_is'45'equiv'45'map'45'inv'45'idempotent'45'trunc'45'Prop_216 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'map'45'inv'45'idempotent'45'trunc'45'Prop_216 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qpropositions.du_is'45'equiv'45'is'45'prop_140
      (coe du_map'45'idempotent'45'trunc'45'Prop_210 (coe v0))
-- foundation.propositional-truncations._.inv-idempotent-trunc-Prop
d_inv'45'idempotent'45'trunc'45'Prop_218 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_inv'45'idempotent'45'trunc'45'Prop_218 v0 ~v1
  = du_inv'45'idempotent'45'trunc'45'Prop_218 v0
du_inv'45'idempotent'45'trunc'45'Prop_218 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_inv'45'idempotent'45'trunc'45'Prop_218 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe du_unit'45'trunc'45'Prop_12 (coe v0))
      (coe
         du_is'45'equiv'45'map'45'inv'45'idempotent'45'trunc'45'Prop_216
         (coe v0))
-- foundation.propositional-truncations.dependent-universal-property-trunc-Prop
d_dependent'45'universal'45'property'45'trunc'45'Prop_226 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_dependent'45'universal'45'property'45'trunc'45'Prop_226 v0 ~v1
                                                          ~v2
  = du_dependent'45'universal'45'property'45'trunc'45'Prop_226 v0
du_dependent'45'universal'45'property'45'trunc'45'Prop_226 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_dependent'45'universal'45'property'45'trunc'45'Prop_226 v0
  = coe
      MAlonzo.Code.Qfoundation.QuniversalZ45ZpropertyZ45ZpropositionalZ45Ztruncation.du_dependent'45'universal'45'property'45'is'45'propositional'45'truncation_456
      (coe v0) (coe d_trunc'45'Prop_32 v0 erased)
      (coe du_unit'45'trunc'45'Prop_12 (coe v0))
      (coe
         (\ v1 ->
            coe
              du_is'45'propositional'45'truncation'45'trunc'45'Prop_148 (coe v0)
              (coe v1)))
-- foundation.propositional-truncations._.equiv-dependent-universal-property-trunc-Prop
d_equiv'45'dependent'45'universal'45'property'45'trunc'45'Prop_246 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'dependent'45'universal'45'property'45'trunc'45'Prop_246 v0
                                                                   ~v1 ~v2 v3
  = du_equiv'45'dependent'45'universal'45'property'45'trunc'45'Prop_246
      v0 v3
du_equiv'45'dependent'45'universal'45'property'45'trunc'45'Prop_246 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'dependent'45'universal'45'property'45'trunc'45'Prop_246 v0
                                                                    v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.Qfunctions.du_precomp'45'Π_82
         (coe du_unit'45'trunc'45'Prop_12 (coe v0)))
      (coe
         du_dependent'45'universal'45'property'45'trunc'45'Prop_226 v0 v1)
-- foundation.propositional-truncations._.apply-dependent-universal-property-trunc-Prop
d_apply'45'dependent'45'universal'45'property'45'trunc'45'Prop_252 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d_apply'45'dependent'45'universal'45'property'45'trunc'45'Prop_252 v0
                                                                   ~v1 ~v2 v3 v4 v5
  = du_apply'45'dependent'45'universal'45'property'45'trunc'45'Prop_252
      v0 v3 v4 v5
du_apply'45'dependent'45'universal'45'property'45'trunc'45'Prop_252 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
du_apply'45'dependent'45'universal'45'property'45'trunc'45'Prop_252 v0
                                                                    v1 v2 v3
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'inv'45'equiv_240
      (coe
         du_equiv'45'dependent'45'universal'45'property'45'trunc'45'Prop_246
         (coe v0) (coe v1))
      v3 v2
-- foundation.propositional-truncations.equiv-prod-trunc-Prop
d_equiv'45'prod'45'trunc'45'Prop_266 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'prod'45'trunc'45'Prop_266 v0 v1 ~v2 ~v3
  = du_equiv'45'prod'45'trunc'45'Prop_266 v0 v1
du_equiv'45'prod'45'trunc'45'Prop_266 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_equiv'45'prod'45'trunc'45'Prop_266 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QcontractibleZ45Ztypes.du_center_18
         (coe
            MAlonzo.Code.Qfoundation.QuniversalZ45ZpropertyZ45ZpropositionalZ45Ztruncation.du_is'45'uniquely'45'unique'45'propositional'45'truncation_424
            (coe ()) (coe ()) (coe ()) (coe d_trunc'45'Prop_32 () erased)
            (coe
               MAlonzo.Code.QfoundationZ45Zcore.Qpropositions.du_prod'45'Prop_292
               (coe d_trunc'45'Prop_32 v0 erased)
               (coe d_trunc'45'Prop_32 v1 erased))
            (coe du_unit'45'trunc'45'Prop_12 (coe ()))
            (coe
               MAlonzo.Code.Qfoundation.QfunctorialityZ45ZcartesianZ45ZproductZ45Ztypes.du_map'45'prod_28
               (coe du_unit'45'trunc'45'Prop_12 (coe v0))
               (coe du_unit'45'trunc'45'Prop_12 (coe v1)))
            (coe
               (\ v2 ->
                  coe
                    du_is'45'propositional'45'truncation'45'trunc'45'Prop_148 (coe ())
                    (coe v2)))
            (coe
               MAlonzo.Code.Qfoundation.QuniversalZ45ZpropertyZ45ZpropositionalZ45Ztruncation.du_is'45'propositional'45'truncation'45'prod_680
               (coe v0) (coe v1)
               (coe
                  (\ v2 ->
                     coe
                       du_is'45'propositional'45'truncation'45'trunc'45'Prop_148 (coe v0)
                       (coe v2)))
               (coe
                  (\ v2 ->
                     coe
                       du_is'45'propositional'45'truncation'45'trunc'45'Prop_148 (coe v1)
                       (coe v2))))))
-- foundation.propositional-truncations.map-distributive-trunc-prod-Prop
d_map'45'distributive'45'trunc'45'prod'45'Prop_280 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_map'45'distributive'45'trunc'45'prod'45'Prop_280 v0 v1 ~v2 ~v3
  = du_map'45'distributive'45'trunc'45'prod'45'Prop_280 v0 v1
du_map'45'distributive'45'trunc'45'prod'45'Prop_280 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_map'45'distributive'45'trunc'45'prod'45'Prop_280 v0 v1
  = coe
      du_map'45'universal'45'property'45'trunc'45'Prop_176 (coe ())
      (coe ())
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         erased
         (coe
            MAlonzo.Code.QfoundationZ45Zcore.Qpropositions.du_is'45'prop'45'prod_280
            (coe du_is'45'prop'45'type'45'trunc'45'Prop_18 (coe v0))
            (coe du_is'45'prop'45'type'45'trunc'45'Prop_18 (coe v1))))
      (coe
         MAlonzo.Code.Qfoundation.QfunctorialityZ45ZcartesianZ45ZproductZ45Ztypes.du_map'45'prod_28
         (coe du_unit'45'trunc'45'Prop_12 (coe v0))
         (coe du_unit'45'trunc'45'Prop_12 (coe v1)))
-- foundation.propositional-truncations.map-inv-distributive-trunc-prod-Prop
d_map'45'inv'45'distributive'45'trunc'45'prod'45'Prop_298 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny
d_map'45'inv'45'distributive'45'trunc'45'prod'45'Prop_298 v0 v1 ~v2
                                                          ~v3 v4
  = du_map'45'inv'45'distributive'45'trunc'45'prod'45'Prop_298
      v0 v1 v4
du_map'45'inv'45'distributive'45'trunc'45'prod'45'Prop_298 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny
du_map'45'inv'45'distributive'45'trunc'45'prod'45'Prop_298 v0 v1 v2
  = coe
      du_map'45'universal'45'property'45'trunc'45'Prop_176 v0 ()
      (coe d_trunc'45'Prop_32 () erased)
      (\ v3 ->
         coe
           du_map'45'universal'45'property'45'trunc'45'Prop_176 v1 ()
           (coe d_trunc'45'Prop_32 () erased)
           (coe
              MAlonzo.Code.QfoundationZ45Zcore.Qfunctions.du__'8728'__36
              (coe (\ v4 -> coe du_unit'45'trunc'45'Prop_12 (coe ())))
              (coe
                 MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
                 (coe v3)))
           (MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr2_28
              (coe v2)))
      (MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
         (coe v2))
-- foundation.propositional-truncations.is-equiv-map-distributive-trunc-prod-Prop
d_is'45'equiv'45'map'45'distributive'45'trunc'45'prod'45'Prop_320 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'map'45'distributive'45'trunc'45'prod'45'Prop_320 v0
                                                                  v1 ~v2 ~v3
  = du_is'45'equiv'45'map'45'distributive'45'trunc'45'prod'45'Prop_320
      v0 v1
du_is'45'equiv'45'map'45'distributive'45'trunc'45'prod'45'Prop_320 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'map'45'distributive'45'trunc'45'prod'45'Prop_320 v0
                                                                   v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qpropositions.du_is'45'equiv'45'is'45'prop_140
      (coe
         du_map'45'inv'45'distributive'45'trunc'45'prod'45'Prop_298 (coe v0)
         (coe v1))
-- foundation.propositional-truncations.distributive-trunc-prod-Prop
d_distributive'45'trunc'45'prod'45'Prop_338 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_distributive'45'trunc'45'prod'45'Prop_338 v0 v1 ~v2 ~v3
  = du_distributive'45'trunc'45'prod'45'Prop_338 v0 v1
du_distributive'45'trunc'45'prod'45'Prop_338 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_distributive'45'trunc'45'prod'45'Prop_338 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         du_map'45'distributive'45'trunc'45'prod'45'Prop_280 (coe v0)
         (coe v1))
      (coe
         du_is'45'equiv'45'map'45'distributive'45'trunc'45'prod'45'Prop_320
         (coe v0) (coe v1))
-- foundation.propositional-truncations.is-equiv-map-inv-distributive-trunc-prod-Prop
d_is'45'equiv'45'map'45'inv'45'distributive'45'trunc'45'prod'45'Prop_348 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'map'45'inv'45'distributive'45'trunc'45'prod'45'Prop_348 v0
                                                                         v1 ~v2 ~v3
  = du_is'45'equiv'45'map'45'inv'45'distributive'45'trunc'45'prod'45'Prop_348
      v0 v1
du_is'45'equiv'45'map'45'inv'45'distributive'45'trunc'45'prod'45'Prop_348 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'map'45'inv'45'distributive'45'trunc'45'prod'45'Prop_348 v0
                                                                          v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qpropositions.du_is'45'equiv'45'is'45'prop_140
      (coe
         du_map'45'distributive'45'trunc'45'prod'45'Prop_280 (coe v0)
         (coe v1))
-- foundation.propositional-truncations.inv-distributive-trunc-prod-Prop
d_inv'45'distributive'45'trunc'45'prod'45'Prop_366 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_inv'45'distributive'45'trunc'45'prod'45'Prop_366 v0 v1 ~v2 ~v3
  = du_inv'45'distributive'45'trunc'45'prod'45'Prop_366 v0 v1
du_inv'45'distributive'45'trunc'45'prod'45'Prop_366 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_inv'45'distributive'45'trunc'45'prod'45'Prop_366 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         du_map'45'inv'45'distributive'45'trunc'45'prod'45'Prop_298 (coe v0)
         (coe v1))
      (coe
         du_is'45'equiv'45'map'45'inv'45'distributive'45'trunc'45'prod'45'Prop_348
         (coe v0) (coe v1))
